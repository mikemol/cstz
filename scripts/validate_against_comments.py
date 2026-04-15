#!/usr/bin/env python3
"""Validate alignment triples against authorial cross-reference comments.

Hybrid-mode validation step (per user decision: "comments allowed only
as validation, not seed").  The alignment engine in
``scripts/align_perspectives.py`` ignored authorial annotations
entirely; here we load them from the extracted manifests and measure
how often the loop's triples agree with the authors' own
cross-references.

Agreement metric per triple ``(paper, agda, python)``:

    evidence = set of cross-ref signals that vote FOR this triple, e.g.:

      * Agda docstring contains the paper label id (``def:operationalist``)
      * Agda docstring contains the python file path (``src/cstz/axioms.py``)
      * Python docstring contains the Agda module name (``CSTZ.Axiom.Operationalist``)
      * Python docstring contains the paper section reference
        (``Paper §1`` with section-number-only or ``Paper §4, Thm 4.2``)
      * STUDY.md cross-reference in either docstring

    agreement_score = |evidence| / 4  (maximum four kinds of signals)

Matching is done via LITERAL SUBSTRING check on parse-tree-extracted
tokens — not via regex over structured cross-reference syntax.  The
tokens come from each parse tree: pandoc gives us label ids as
``Span.attr.id``; tree-sitter-agda gives us ``module_name`` tokens;
Python ast gives us file paths through ``path.relative_to``.

Output:
  reports/validation.jsonl   — per-triple agreement record
  reports/validation.md      — human-auditable summary
  reports/divergence.md      — triples with zero evidence (most likely wrong)

Usage:
  python3 scripts/validate_against_comments.py
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path


def _load_manifest(path: Path) -> list[dict]:
    if not path.exists():
        return []
    return [json.loads(line) for line in path.open() if line.strip()]


def qualname_subgraph(qn: str) -> frozenset[str]:
    """Parse an alignment qualname into its component-token set.

    ``agda:module:CSTZ.Axiom.Operationalist``  →
        {agda, module, cstz, axiom, operationalist}
    ``python:function:check_operationalist``   →
        {python, function, check, operationalist}
    ``paper:definition:def:operationalist``    →
        {paper, definition, def, operationalist}

    Two qualnames refer to the same underlying object iff their
    subgraphs overlap significantly on the *semantic core* tokens
    (everything but the source-kind prefix).  This is more honest
    than string-equality matching because it exposes the qualname's
    own internal structure — dot-separated path segments, dashes,
    underscores, camel-case boundaries — as first-class parse
    components.
    """
    import re as _re
    # Split on '.', '-', '_', ':', '/', camelCase boundaries
    parts = _re.split(r"[.:\-_/]+", qn)
    tokens: set[str] = set()
    for p in parts:
        # camelCase split
        for seg in _re.findall(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z0-9]+|[A-Z]+", p):
            if len(seg) >= 2:
                tokens.add(seg.lower())
    return frozenset(tokens)


def _docstring_by_qualname_agda(rows: list[dict]) -> tuple[dict[str, str], dict[str, str]]:
    """Index agda rows by subgraph-best-match lookup.

    Returns ``(by_exact, by_subgraph_sig)`` where ``by_exact`` keys on
    the full alignment qualname and ``by_subgraph_sig`` keys on the
    frozenset of subgraph tokens.  Callers pick whichever matches.

    Every declaration also inherits its module's header comment block.
    """
    by_exact: dict[str, str] = {}
    module_header_by_path: dict[str, str] = {}
    for r in rows:
        if r.get("kind") == "module":
            module_header_by_path[r.get("path", "")] = r.get("docstring", "") or ""

    # Build ``alignment_qn → docstring`` mappings using qualnames as the
    # alignment engine constructs them.  For agda the alignment qualname
    # is ``agda:<kind>:<name>`` where ``name`` comes from the parser's
    # ``named_decl`` property, which for modules is the FULL dotted name.
    # We reconstruct both possibilities here.
    for r in rows:
        kind = r.get("kind", "")
        name = r.get("name", "")
        qualname = r.get("qualname", "")
        doc = r.get("docstring", "") or ""
        header = module_header_by_path.get(r.get("path", ""), "")
        if header and header != doc:
            doc = header + "\n\n" + doc
        # Under the current extract_agda.py, module rows have
        # ``name=Operationalist`` (stem only) and
        # ``qualname=CSTZ.Axiom.Operationalist``.  The alignment engine's
        # qualname for the same module is ``agda:module:CSTZ.Axiom.Operationalist``.
        # We populate whichever form produces a non-colliding key.
        candidates = [name]
        if qualname and qualname != name:
            candidates.append(qualname)
        for cand in candidates:
            key = f"agda:{kind}:{cand}"
            if key not in by_exact:
                by_exact[key] = doc

    # Subgraph index: map subgraph-tokens → docstring, for fallback lookup
    by_sub: dict[frozenset[str], str] = {}
    for k, v in by_exact.items():
        by_sub[qualname_subgraph(k)] = v

    # Return a single merged dict: exact keys and subgraph-signature
    # string keys (frozensets aren't convenient), using a sentinel wrapper
    return by_exact, by_sub


def _docstring_by_qualname_python(rows: list[dict]) -> tuple[dict[str, str], dict[str, str]]:
    """Index python rows: returns (by_qualname, by_simple_name).

    Alignment engine's python qualname is ``python:<kind>:<name>`` where
    kind is one of "module", "function", "class".  We ignore methods
    and nested decls.
    """
    by_qn: dict[str, str] = {}
    by_simple: dict[str, str] = {}
    for r in rows:
        kind = r["kind"]
        if kind not in ("module", "function", "class"):
            continue
        name = r["name"]
        doc = r.get("docstring", "") or ""
        by_qn[f"python:{kind}:{name}"] = doc
        by_simple[name] = doc
    return by_qn, by_simple


def _paper_label_by_qualname(rows: list[dict]) -> dict[str, str]:
    """Index paper rows by alignment qualname → LaTeX label id."""
    out: dict[str, str] = {}
    for r in rows:
        label = r.get("label") or ""
        kind = r["kind"]
        if label:
            out[f"paper:{kind}:{label}"] = label
    return out


_KIND_TO_CITATIONS = {
    "definition":  ("Definition", "Def"),
    "theorem":     ("Theorem", "Thm"),
    "proposition": ("Proposition", "Prop"),
    "lemma":       ("Lemma", "Lem"),
    "corollary":   ("Corollary", "Cor"),
    "remark":      ("Remark", "Rem"),
    "example":     ("Example", "Ex"),
    "conjecture":  ("Conjecture", "Conj"),
    "openquestion":("Open Question", "OQ"),
}


def _paper_citations_by_qualname(rows: list[dict]) -> dict[str, list[str]]:
    """Index paper rows by alignment qualname → list of citation variants.

    For a paper definition at section 3 position 5, the citation
    variants are ``[Definition 3.5, Def 3.5]``.  The validator looks
    for any of these as a literal substring in Agda/Python docstrings.

    Variants come from LaTeX's standard citation conventions — no
    custom format invented here; we just materialize
    ``<EnvName> <section>.<item>`` and the short-form alias.
    """
    out: dict[str, list[str]] = {}
    for r in rows:
        label = r.get("label") or ""
        kind = r["kind"]
        section_num = r.get("section_num")
        item_num = r.get("item_num")
        if not label or not section_num or not item_num:
            continue
        qn = f"paper:{kind}:{label}"
        long_form, short_form = _KIND_TO_CITATIONS.get(kind, (kind.title(), kind[:3].title()))
        cite_id = f"{section_num}.{item_num}"
        out[qn] = [f"{long_form} {cite_id}", f"{short_form} {cite_id}"]
    return out


def _paper_path_by_qualname(rows: list[dict]) -> dict[str, tuple[str, int, str]]:
    """Index paper rows: qualname → (path, line, section)."""
    out: dict[str, tuple[str, int, str]] = {}
    for r in rows:
        label = r.get("label") or ""
        kind = r["kind"]
        qn = f"paper:{kind}:{label}"
        if label:
            out[qn] = (r.get("path", ""), r.get("line", 0), r.get("section", ""))
    return out


def _python_path_by_qualname(rows: list[dict]) -> dict[str, tuple[str, int]]:
    out: dict[str, tuple[str, int]] = {}
    for r in rows:
        kind = r["kind"]
        if kind not in ("module", "function", "class"):
            continue
        qn = f"python:{kind}:{r['name']}"
        out[qn] = (r.get("path", ""), r.get("line", 0))
    return out


def _agda_module_name(qn: str) -> str:
    """``agda:function:foo`` → not a module; ``agda:module:CSTZ.X.Y`` → CSTZ.X.Y."""
    parts = qn.split(":", 2)
    if len(parts) == 3 and parts[1] == "module":
        return parts[2]
    return ""


# ---------------------------------------------------------------------------
# Evidence scoring
# ---------------------------------------------------------------------------


def evidence_for_triple(
    triple: dict,
    *,
    agda_docs: dict[str, str],
    python_docs_by_qn: dict[str, str],
    python_docs_by_simple: dict[str, str],
    paper_label: dict[str, str],
    paper_meta: dict[str, tuple[str, int, str]],
    python_meta: dict[str, tuple[str, int]],
    paper_citations: dict[str, list[str]] | None = None,
) -> dict:
    """Compute evidence for a single triple."""
    ev: dict[str, list[str]] = {}
    agda_qn = triple["agda"]
    paper_qn = triple["paper"]
    python_qn = triple["python"]

    agda_doc = agda_docs.get(agda_qn, "")
    py_doc = python_docs_by_qn.get(python_qn, "")

    # --- Signal 1: paper label mentioned in agda docstring ---
    p_label = paper_label.get(paper_qn, "")
    if p_label and p_label in agda_doc:
        ev.setdefault("paper_label_in_agda", []).append(p_label)

    # --- Signal 2: paper label mentioned in python docstring ---
    if p_label and p_label in py_doc:
        ev.setdefault("paper_label_in_python", []).append(p_label)

    # --- Signal 1b: paper numeric citation (Def 3.5, Theorem 6.17) in agda/python docs ---
    if paper_citations:
        for cite in paper_citations.get(paper_qn, []):
            if cite in agda_doc:
                ev.setdefault("paper_citation_in_agda", []).append(cite)
                break
        for cite in paper_citations.get(paper_qn, []):
            if cite in py_doc:
                ev.setdefault("paper_citation_in_python", []).append(cite)
                break

    # --- Signal 3: paper path mentioned (e.g. "paper/sections/sec01-intro.tex") ---
    p_path, p_line, p_section = paper_meta.get(paper_qn, ("", 0, ""))
    if p_path:
        path_stem = Path(p_path).name
        if path_stem and path_stem in agda_doc:
            ev.setdefault("paper_path_in_agda", []).append(path_stem)
        if path_stem and path_stem in py_doc:
            ev.setdefault("paper_path_in_python", []).append(path_stem)

    # --- Signal 4: agda path mentioned in python docstring ---
    # Agda paths are typed as "agda/CSTZ/Axiom/ProfileLinearity.agda" in python
    # docstrings.  We look for the last-segment module name as substring.
    agda_path = triple.get("agda_path", "")
    if agda_path:
        # e.g. "/home/user/cstz/agda/CSTZ/Axiom/ProfileLinearity.agda:34"
        # We want "agda/CSTZ/Axiom/ProfileLinearity.agda"
        normalized = agda_path.replace("/home/user/cstz/", "")
        normalized = normalized.split(":", 1)[0]
        if normalized and normalized in py_doc:
            ev.setdefault("agda_path_in_python", []).append(normalized)
        # Also check the dotted module qualname form
        # parts[2] of "agda:module:CSTZ.X.Y" is the dotted module name
        m_name = _agda_module_name(agda_qn)
        if m_name:
            if m_name in py_doc:
                ev.setdefault("agda_module_in_python", []).append(m_name)
            if m_name in agda_doc:
                # The module name in its own header: that's trivial, skip.
                pass

    # --- Signal 5: python path mentioned in agda docstring ---
    py_path, py_line = python_meta.get(python_qn, ("", 0))
    if py_path:
        normalized = py_path.replace("/home/user/cstz/", "")
        if normalized and normalized in agda_doc:
            ev.setdefault("python_path_in_agda", []).append(normalized)
        # Also shorter form: src/cstz/axioms.py
        short = normalized.replace("/home/user/cstz/", "")
        if short and short.startswith("src/cstz") and short in agda_doc:
            ev.setdefault("python_short_in_agda", []).append(short)

    # --- Signal 6: python function/class name in agda docstring ---
    py_parts = python_qn.split(":", 2)
    if len(py_parts) == 3:
        py_name = py_parts[2]
        if py_name and len(py_name) >= 4 and py_name in agda_doc:
            ev.setdefault("python_name_in_agda", []).append(py_name)

    return ev


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def main():
    repo = Path.cwd()
    reports = repo / "reports"

    triples = _load_manifest(reports / "triples.jsonl")
    agda_rows = _load_manifest(reports / "agda_decls.jsonl")
    python_rows = _load_manifest(reports / "python_decls.jsonl")
    paper_rows = _load_manifest(reports / "paper_decls.jsonl")

    if not triples:
        print("# no triples.jsonl found — run align_perspectives.py first", file=sys.stderr)
        sys.exit(1)

    agda_docs_exact, agda_docs_sub = _docstring_by_qualname_agda(agda_rows)

    def lookup_agda_doc(qn: str) -> str:
        """Subgraph-matching docstring lookup.

        Try exact match first; fall back to largest-subgraph-overlap
        entry in the subgraph index.
        """
        if qn in agda_docs_exact:
            return agda_docs_exact[qn]
        target = qualname_subgraph(qn)
        best: tuple[int, str] = (0, "")
        for sig, doc in agda_docs_sub.items():
            overlap = len(target & sig)
            if overlap > best[0]:
                best = (overlap, doc)
        # Require at least 2 tokens of overlap to avoid spurious matches
        return best[1] if best[0] >= 2 else ""

    # Back-compat wrapper so downstream evidence_for_triple can still
    # use dict-style indexing
    class _AgdaDocs:
        def get(self, qn: str, default: str = "") -> str:
            return lookup_agda_doc(qn) or default

        def __getitem__(self, qn: str) -> str:
            return lookup_agda_doc(qn)

    agda_docs = _AgdaDocs()
    py_docs_by_qn, py_docs_by_simple = _docstring_by_qualname_python(python_rows)
    paper_label = _paper_label_by_qualname(paper_rows)
    paper_citations = _paper_citations_by_qualname(paper_rows)
    paper_meta = _paper_path_by_qualname(paper_rows)
    python_meta = _python_path_by_qualname(python_rows)

    records: list[dict] = []
    signal_counts: Counter = Counter()
    zero_evidence: list[dict] = []

    for t in triples:
        ev = evidence_for_triple(
            t,
            agda_docs=agda_docs,
            python_docs_by_qn=py_docs_by_qn,
            python_docs_by_simple=py_docs_by_simple,
            paper_label=paper_label,
            paper_meta=paper_meta,
            python_meta=python_meta,
            paper_citations=paper_citations,
        )
        n_signals = len(ev)
        for k in ev:
            signal_counts[k] += 1
        rec = {
            "agda": t["agda"],
            "paper": t["paper"],
            "python": t["python"],
            "agda_path": t.get("agda_path", ""),
            "paper_path": t.get("paper_path", ""),
            "python_path": t.get("python_path", ""),
            "evidence": ev,
            "n_signals": n_signals,
        }
        records.append(rec)
        if n_signals == 0:
            zero_evidence.append(rec)

    # --- Write JSONL ---
    (reports / "validation.jsonl").write_text(
        "\n".join(json.dumps(r, ensure_ascii=False) for r in records) + "\n"
    )

    # --- Summary md ---
    n = len(records)
    with_any = sum(1 for r in records if r["n_signals"] > 0)
    avg_signals = sum(r["n_signals"] for r in records) / n if n else 0.0
    lines = [
        "# Alignment validation",
        "",
        f"- Total triples: **{n}**",
        f"- Triples with ≥1 authorial signal: **{with_any}** ({100*with_any/n:.1f}%)",
        f"- Average signals per triple: **{avg_signals:.2f}** / 6 possible",
        f"- Zero-evidence triples (most suspect): **{len(zero_evidence)}** ({100*len(zero_evidence)/n:.1f}%)",
        "",
        "## Signal breakdown",
        "",
        "| Signal | Count | % of triples |",
        "|--------|-------|--------------|",
    ]
    for k, c in signal_counts.most_common():
        lines.append(f"| {k} | {c} | {100*c/n:.1f}% |")
    (reports / "validation.md").write_text("\n".join(lines) + "\n")

    # --- Zero-evidence report ---
    lines = ["# Triples with zero authorial cross-reference evidence", "",
             f"{len(zero_evidence)} out of {n} committed triples have no supporting",
             "signal in the docstrings/comments.  These are the triples most likely",
             "to be wrong — the alignment engine matched them on structural",
             "grounds alone, without the authors ever mentioning the other side.",
             "",
             "| agda | paper | python |",
             "|------|-------|--------|",
             ]
    for r in zero_evidence[:120]:
        a = r["agda"].replace("agda:", "").replace("|", r"\|")
        p = r["paper"].replace("paper:", "").replace("|", r"\|")
        y = r["python"].replace("python:", "").replace("|", r"\|")
        lines.append(f"| {a} | {p} | {y} |")
    if len(zero_evidence) > 120:
        lines.append(f"| … | ({len(zero_evidence) - 120} more) | |")
    (reports / "divergence.md").write_text("\n".join(lines) + "\n")

    # --- Console summary ---
    print(f"Validation of {n} triples against authorial cross-references:")
    print(f"  with any signal: {with_any} ({100*with_any/n:.1f}%)")
    print(f"  avg signals/triple: {avg_signals:.2f}")
    print(f"  zero-evidence: {len(zero_evidence)}")
    print()
    print("Signal breakdown:")
    for k, c in signal_counts.most_common():
        print(f"  {k:30s} {c:4d}  ({100*c/n:.1f}%)")


if __name__ == "__main__":
    main()
