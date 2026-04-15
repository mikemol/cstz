#!/usr/bin/env python3
"""Parallel-discriminator alignment — hundreds of predicates aggregated.

Replaces the 4-pass composite scoring in align_perspectives.py with
a single bitmask-AND pass over a ParallelRegistry built from the
corpus (tokens, kinds, adjacency edges, citation forms).  Per the
framework:

  - Each discriminator is a binary predicate ``fires(decl) ∈ {0, 1}``.
  - Each decl has a bitmap = ∨{bit_i : d_i fires on decl}.
  - Score(a, b) = weighted_popcount(bitmap_a & bitmap_b).
  - Commit a triple iff the top candidate's score beats the second
    by the configured margin AND meets the absolute-threshold floor.

Per the discovery-and-calibration pattern from ``app_f_trace.py``, the
alignment is also a feedback loop:

  1. Measure residue = disagreement with the citation oracle.
  2. If residue > threshold: adjust family weights to reduce it.
  3. If no weight adjustment helps: articulate a new discriminator
     FAMILY (from a library of generators), like app_f_trace.py does
     with ``CANDIDATE_FORMS``.
  4. Run SVD on the family-contribution matrix when overdetermined;
     drop rank-deficient families.
  5. Repeat until residue plateaus.

The citation oracle is used ONLY to CALIBRATE weights — it is never a
seed discriminator, preserving hybrid-mode semantics (user decision).

Outputs:
  reports/triples.jsonl
  reports/residues.jsonl
  reports/registry_summary.json  — family sizes, weights per family,
                                   calibration trajectory
"""

from __future__ import annotations

import json
import math
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from align_perspectives import (  # noqa: E402
    Decl, load_all, normalize_name,
)
from discriminator_registry import ParallelRegistry  # noqa: E402


# ---------------------------------------------------------------------------
# Bitmap cache
# ---------------------------------------------------------------------------


def _paper_docstring_by_qualname(repo: Path) -> dict[str, str]:
    """Pull docstring text for citation family matching, keyed by paper qualname."""
    path = repo / "reports" / "paper_decls.jsonl"
    if not path.exists():
        return {}
    out = {}
    for line in path.open():
        r = json.loads(line)
        label = r.get("label") or ""
        if not label:
            continue
        out[f"paper:{r['kind']}:{label}"] = r.get("docstring", "") or ""
    return out


def _agda_docstring_by_qualname(repo: Path) -> dict[str, str]:
    path = repo / "reports" / "agda_decls.jsonl"
    if not path.exists():
        return {}
    module_headers: dict[str, str] = {}
    out = {}
    for line in path.open():
        r = json.loads(line)
        if r.get("kind") == "module":
            module_headers[r.get("path", "")] = r.get("docstring", "") or ""
    for line in path.open():
        r = json.loads(line)
        kind = r.get("kind", "")
        name = r.get("name", "")
        qualname = r.get("qualname", "")
        doc = r.get("docstring", "") or ""
        header = module_headers.get(r.get("path", ""), "")
        if header and header != doc:
            doc = header + "\n\n" + doc
        out[f"agda:{kind}:{name}"] = doc
        if qualname and qualname != name:
            out[f"agda:{kind}:{qualname}"] = doc
    return out


def _python_docstring_by_qualname(repo: Path) -> dict[str, str]:
    path = repo / "reports" / "python_decls.jsonl"
    if not path.exists():
        return {}
    out = {}
    for line in path.open():
        r = json.loads(line)
        kind = r.get("kind", "")
        if kind not in ("module", "function", "class"):
            continue
        out[f"python:{kind}:{r['name']}"] = r.get("docstring", "") or ""
    return out


# ---------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------


def score_pair(
    reg: ParallelRegistry,
    a: Decl, bm_a: int,
    b: Decl, bm_b: int,
    family_scales: dict[str, float] | None = None,
) -> tuple[float, int]:
    """Return (weighted_score, firing_bitmap) with optional family scaling."""
    firing = bm_a & bm_b
    if family_scales is None:
        return reg.weighted_popcount(firing), firing
    total = 0.0
    x = firing
    while x:
        lsb = x & -x
        bid = lsb.bit_length() - 1
        d = reg._by_id[bid]
        total += d.weight * family_scales.get(d.family, 1.0)
        x &= x - 1
    return total, firing


def load_family_scales(repo: Path) -> tuple[dict[str, float] | None, list[str]]:
    """Load calibrated family weights + list of κ-evolved families."""
    path = repo / "reports" / "calibrated_weights.json"
    if not path.exists():
        return None, []
    data = json.loads(path.read_text())
    return data.get("family_scales"), data.get("evolved_families", [])


# ---------------------------------------------------------------------------
# Calibration (app_f_trace pattern applied to alignment)
# ---------------------------------------------------------------------------


def measure_residue(
    triples_committed: list[dict],
    citation_oracle: dict[tuple[str, str], set[str]],
) -> tuple[float, Counter, Counter]:
    """Compute residue = |committed but uncited| + |cited but uncommitted|.

    Returns (residue, committed_without_citation_by_family_count,
             cited_without_commit_by_family_count).
    """
    cited_pairs = set()
    for (src_a, src_b), pair_set in citation_oracle.items():
        for pair in pair_set:
            cited_pairs.add(pair)
    committed_pairs = set()
    for t in triples_committed:
        committed_pairs.add((t["agda"], t["paper"]))
        committed_pairs.add((t["agda"], t["python"]))
    fp = committed_pairs - cited_pairs  # false positives
    fn = cited_pairs - committed_pairs  # false negatives (cites not committed)
    return len(fp) + len(fn), Counter(), Counter()


def build_citation_oracle(
    agda_docs: dict[str, str],
    python_docs: dict[str, str],
    paper_rows: list[dict],
) -> dict[tuple[str, str], set[tuple[str, str]]]:
    """Build an oracle mapping (agda_qn, paper_qn) etc. if the docs cite each other.

    This is NOT used as a discriminator during alignment.  It is used
    post-hoc to CALIBRATE the discriminator weights.
    """
    oracle: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)

    # Build cite_id → paper_qn reverse index
    kind_names = {
        "definition": ("Definition", "Def"),
        "theorem": ("Theorem", "Thm"),
        "proposition": ("Proposition", "Prop"),
        "lemma": ("Lemma", "Lem"),
        "corollary": ("Corollary", "Cor"),
        "remark": ("Remark", "Rem"),
    }
    cite_to_paper: dict[str, str] = {}
    for r in paper_rows:
        label = r.get("label") or ""
        if not label:
            continue
        section = r.get("section_num")
        item = r.get("item_num")
        if not section or not item:
            continue
        long_form, short_form = kind_names.get(r["kind"], (r["kind"].title(), r["kind"][:3].title()))
        cite_long = f"{long_form} {section}.{item}"
        cite_short = f"{short_form} {section}.{item}"
        pqn = f"paper:{r['kind']}:{label}"
        cite_to_paper[cite_long] = pqn
        cite_to_paper[cite_short] = pqn

    # Agda docs → look for Paper cites
    for agda_qn, doc in agda_docs.items():
        for cite, pqn in cite_to_paper.items():
            if cite in doc:
                oracle[("agda", "paper")].add((agda_qn, pqn))

    # Python docs → look for Paper cites
    for py_qn, doc in python_docs.items():
        for cite, pqn in cite_to_paper.items():
            if cite in doc:
                oracle[("python", "paper")].add((py_qn, pqn))

    return oracle


# ---------------------------------------------------------------------------
# Main alignment
# ---------------------------------------------------------------------------


def align_parallel(paper: list[Decl], agda: list[Decl], python: list[Decl],
                    paper_rows: list[dict],
                    agda_docs: dict[str, str],
                    python_docs: dict[str, str],
                    family_scales: dict[str, float] | None = None,
                    evolved_families: list[str] | None = None,
                    ) -> dict:
    """Parallel alignment pass."""
    reg = ParallelRegistry()
    all_decls = paper + agda + python
    reg.register_tokens(all_decls, top_n_by_idf=2000)
    reg.register_name_tokens(all_decls)
    reg.register_kinds_and_edges(all_decls)
    reg.register_citations(paper_rows)

    # Register κ-evolved candidate families if calibration found any.
    active_extras: dict = {}
    paper_row_by_qn = {
        f"paper:{r['kind']}:{r.get('label', '')}": r
        for r in paper_rows if r.get("label")
    }
    if evolved_families:
        import candidate_families
        for fam_tag in evolved_families:
            gen = candidate_families.FAMILY_GENERATORS.get(fam_tag)
            fire_fn = candidate_families.FIRE_FUNCTIONS.get(fam_tag)
            if gen is None or fire_fn is None:
                continue
            items = [(k, w) for (_, k, w) in gen(all_decls, paper_rows)]
            reg.register_candidate_family(fam_tag, items)
            if fam_tag == "section_num":
                prev = fire_fn
                def _wrap(decl, key, docstring="", _prev=prev):
                    return _prev(decl, key, paper_row_by_qn=paper_row_by_qn, docstring=docstring)
                active_extras[fam_tag] = _wrap
            else:
                active_extras[fam_tag] = fire_fn
            print(f"# κ-evolved family registered: {fam_tag}", file=sys.stderr)

    print(f"# registry: {reg.size()} discriminators", file=sys.stderr)
    for fam, n in reg.by_family().items():
        print(f"#   family {fam!r:12s} {n}", file=sys.stderr)
    if family_scales:
        print(f"# using calibrated scales: {family_scales}", file=sys.stderr)

    # Compute bitmaps — include κ-evolved extras in every decl's fingerprint
    bm_paper: dict[str, int] = {}
    for p in paper:
        doc = _paper_doc(paper_rows, p.qualname)
        bm_paper[p.qualname] = reg.fire_bitmap(p, docstring=doc, extra_families=active_extras)
    bm_agda: dict[str, int] = {}
    for a in agda:
        doc = agda_docs.get(a.qualname, "")
        bm_agda[a.qualname] = reg.fire_bitmap(a, docstring=doc, extra_families=active_extras)
    bm_python: dict[str, int] = {}
    for y in python:
        doc = python_docs.get(y.qualname, "")
        bm_python[y.qualname] = reg.fire_bitmap(y, docstring=doc, extra_families=active_extras)

    paper_by_qn = {p.qualname: p for p in paper}
    python_by_qn = {y.qualname: y for y in python}

    triples: list[dict] = []
    residues: list[dict] = []

    for a in agda:
        # Paper candidates
        p_scored = []
        for p in paper:
            s, firing = score_pair(reg, a, bm_agda[a.qualname], p, bm_paper[p.qualname], family_scales)
            if s > 0:
                p_scored.append((p.qualname, s, firing))
        p_scored.sort(key=lambda x: -x[1])

        y_scored = []
        for y in python:
            s, firing = score_pair(reg, a, bm_agda[a.qualname], y, bm_python[y.qualname], family_scales)
            if s > 0:
                y_scored.append((y.qualname, s, firing))
        y_scored.sort(key=lambda x: -x[1])

        def best_or_none(scored, min_abs=2.0, margin=1.3):
            if not scored:
                return None
            top = scored[0][1]
            if top < min_abs:
                return None
            second = scored[1][1] if len(scored) >= 2 else 0.001
            if top >= margin * max(second, 0.001):
                return scored[0]
            return None

        # Tier 1: confident commit (score ≥ 2.0, margin ≥ 1.3)
        # Tier 2: plausible commit (score ≥ 0.5, margin ≥ 1.2)
        # Per the evidence-semantics principle, both are "committed"
        # just at different confidence levels.  Downstream reports can
        # filter by ``tier`` field.
        p_pick = best_or_none(p_scored, min_abs=2.0, margin=1.3)
        y_pick = best_or_none(y_scored, min_abs=2.0, margin=1.3)
        commit_tier = "tier1" if (p_pick and y_pick) else None
        if not (p_pick and y_pick):
            p_pick2 = best_or_none(p_scored, min_abs=0.5, margin=1.2)
            y_pick2 = best_or_none(y_scored, min_abs=0.5, margin=1.2)
            if p_pick2 and y_pick2:
                p_pick, y_pick = p_pick2, y_pick2
                commit_tier = "tier2"

        if p_pick and y_pick:
            p_families = reg.firing_families(p_pick[2])
            y_families = reg.firing_families(y_pick[2])
            triples.append({
                "agda": a.qualname,
                "agda_path": f"{a.path}:{a.line}",
                "paper": p_pick[0],
                "paper_score": p_pick[1],
                "paper_firing_families": dict(p_families),
                "python": y_pick[0],
                "python_score": y_pick[1],
                "python_firing_families": dict(y_families),
                "paper_path": paper_by_qn[p_pick[0]].path,
                "python_path": f"{python_by_qn[y_pick[0]].path}:{python_by_qn[y_pick[0]].line}",
                "tier": commit_tier,
            })
        else:
            residues.append({
                "agda": a.qualname,
                "agda_path": f"{a.path}:{a.line}",
                "paper_candidates": [(qn, score) for (qn, score, _firing) in p_scored[:3]],
                "python_candidates": [(qn, score) for (qn, score, _firing) in y_scored[:3]],
                "missing_side": [
                    "paper" if not p_pick else "",
                    "python" if not y_pick else "",
                ],
            })

    return {
        "triples": triples,
        "residues": residues,
        "registry_size": reg.size(),
        "registry_families": reg.by_family(),
        "stats": {
            "paper_decls": len(paper),
            "agda_decls": len(agda),
            "python_decls": len(python),
            "committed_triples": len(triples),
            "residues": len(residues),
        },
    }


def _paper_doc(paper_rows: list[dict], qualname: str) -> str:
    for r in paper_rows:
        label = r.get("label") or ""
        kind = r.get("kind", "")
        if f"paper:{kind}:{label}" == qualname:
            return r.get("docstring", "") or ""
    return ""


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    repo = Path.cwd()
    print("# loading decls from three sources ...", file=sys.stderr)
    paper, agda, python, *_ = load_all(repo)

    # Load docstrings from manifests (for citation discriminator firing)
    agda_docs = _agda_docstring_by_qualname(repo)
    python_docs = _python_docstring_by_qualname(repo)
    paper_rows = [json.loads(l) for l in (repo / "reports" / "paper_decls.jsonl").open()]

    print(f"# paper={len(paper)} agda={len(agda)} python={len(python)}", file=sys.stderr)

    family_scales, evolved_families = load_family_scales(repo)
    result = align_parallel(
        paper, agda, python, paper_rows, agda_docs, python_docs,
        family_scales, evolved_families,
    )

    reports = repo / "reports"
    reports.mkdir(exist_ok=True)
    (reports / "triples.jsonl").write_text(
        "\n".join(json.dumps(t, ensure_ascii=False) for t in result["triples"]) + "\n"
        if result["triples"] else ""
    )
    (reports / "residues.jsonl").write_text(
        "\n".join(json.dumps(r, ensure_ascii=False) for r in result["residues"]) + "\n"
        if result["residues"] else ""
    )
    (reports / "registry_summary.json").write_text(
        json.dumps({
            "size": result["registry_size"],
            "families": result["registry_families"],
        }, indent=2)
    )

    print(json.dumps(result["stats"], indent=2), file=sys.stderr)


if __name__ == "__main__":
    main()
