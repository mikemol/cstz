#!/usr/bin/env python3
"""Calibrate discriminator-family weights against the citation oracle.

This is the app_f_trace.py feedback loop applied to alignment.  Inputs
are the ParallelRegistry from ``align_parallel.py`` and the citation
oracle extracted from ``agda/*.agda`` module headers and ``src/cstz/``
docstrings.  Output is a calibrated ``family_weight_scale`` dict that
rescales every discriminator's weight by its family:

    weight(d) = weight_base(d) * family_weight_scale[d.family]

Calibration loop (one-to-one with ``feedback_loop`` in app_f_trace.py):

  0. Initial family scales: all 1.0.
  1. Build citation oracle: (agda_qn, paper_qn) pairs for each author-
     cited reference from agda docstrings → paper numeric citations.
     (NB: this uses citations only to calibrate, never as a seed
     discriminator during alignment.)
  2. For each ``(agda_qn, paper_qn_oracle)`` pair:
       a. Compute predicted-paper-rank under current family scales.
       b. Residue = predicted_rank - 1  (if oracle_p is not ranked
          first, how far off we are).
  3. Scalar-update family scales: for each family F,
       family_scale[F] *= (1 + η * Δ_F)
     where Δ_F is the correlation between "family F fired on the
     oracle pair" and "oracle pair was promoted up the ranking".
  4. Plateau detection: if mean residue doesn't decrease >5% for 3
     iterations, κ-evolve: emit a report of "stuck discriminators"
     that the registry's current basis can't resolve.  (Adding new
     discriminator families is a follow-up; for now we just surface
     the residue signature.)

Output:
  reports/calibration_trace.jsonl  — per-iteration state (mean_residue,
                                     top-1 accuracy, family_scales)
  reports/calibrated_weights.json  — final family scales
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

from align_perspectives import load_all  # noqa: E402
from discriminator_registry import ParallelRegistry  # noqa: E402
from align_parallel import (  # noqa: E402
    _agda_docstring_by_qualname,
    _python_docstring_by_qualname,
    _paper_doc,
)
import candidate_families  # noqa: E402


# ---------------------------------------------------------------------------
# Citation oracle: parse-tree-to-parse-tree authorial links
# ---------------------------------------------------------------------------


def build_citation_oracle(
    paper_rows: list[dict],
    agda_docs: dict[str, str],
    python_docs: dict[str, str],
) -> list[tuple[str, str, str, str]]:
    """Return list of (oracle_source_qn, target_qn, citation_string, stream_name).

    For each paper decl with a numeric citation (e.g. Def 1.1), scan
    every agda and python docstring for the literal citation.  Each
    hit is an authorial link asserting "this agda/python decl
    references this paper decl".
    """
    kind_names = {
        "definition": ("Definition", "Def"),
        "theorem": ("Theorem", "Thm"),
        "proposition": ("Proposition", "Prop"),
        "lemma": ("Lemma", "Lem"),
        "corollary": ("Corollary", "Cor"),
        "remark": ("Remark", "Rem"),
        "example": ("Example", "Ex"),
        "conjecture": ("Conjecture", "Conj"),
    }
    oracle: list[tuple[str, str, str, str]] = []
    for r in paper_rows:
        section = r.get("section_num")
        item = r.get("item_num")
        label = r.get("label") or ""
        if not section or not item or not label:
            continue
        paper_qn = f"paper:{r['kind']}:{label}"
        long_form, short_form = kind_names.get(r["kind"], (r["kind"].title(), r["kind"][:3].title()))
        cid = f"{section}.{item}"
        cite_long = f"{long_form} {cid}"
        cite_short = f"{short_form} {cid}"
        for src_qn, doc in agda_docs.items():
            if cite_long in doc or cite_short in doc:
                oracle.append((src_qn, paper_qn, cite_long, "agda"))
        for src_qn, doc in python_docs.items():
            if cite_long in doc or cite_short in doc:
                oracle.append((src_qn, paper_qn, cite_long, "python"))
    return oracle


# ---------------------------------------------------------------------------
# Scored-rank predictor under family scales
# ---------------------------------------------------------------------------


def score_with_scales(
    reg: ParallelRegistry,
    bm_a: int, bm_b: int,
    family_scales: dict[str, float],
) -> float:
    """Compute pair score with per-family weight multipliers applied."""
    firing = bm_a & bm_b
    total = 0.0
    x = firing
    while x:
        lsb = x & -x
        bid = lsb.bit_length() - 1
        d = reg._by_id[bid]
        total += d.weight * family_scales.get(d.family, 1.0)
        x &= x - 1
    return total


def predicted_rank(
    reg: ParallelRegistry,
    bm_src: int,
    candidates: list[tuple[str, int]],
    target_qn: str,
    family_scales: dict[str, float],
) -> int:
    """Rank (1 = best) of ``target_qn`` among candidates under current scales."""
    scored = [
        (qn, score_with_scales(reg, bm_src, bm_cand, family_scales))
        for qn, bm_cand in candidates
    ]
    scored.sort(key=lambda x: -x[1])
    for i, (qn, _) in enumerate(scored, start=1):
        if qn == target_qn:
            return i
    return len(candidates) + 1


# ---------------------------------------------------------------------------
# Family-weight gradient step
# ---------------------------------------------------------------------------


def family_contribution(
    reg: ParallelRegistry,
    bm_src: int,
    bm_target: int,
) -> Counter:
    """How much does each family contribute to ``score(src, target)``?"""
    firing = bm_src & bm_target
    out: Counter = Counter()
    x = firing
    while x:
        lsb = x & -x
        bid = lsb.bit_length() - 1
        d = reg._by_id[bid]
        out[d.family] += d.weight
        x &= x - 1
    return out


def gradient_step(
    reg: ParallelRegistry,
    oracle: list[tuple[str, str, str, str]],
    bitmaps: dict[str, int],
    candidates_for_source: dict[str, list[tuple[str, int]]],
    family_scales: dict[str, float],
    eta: float = 0.05,
) -> tuple[dict[str, float], float]:
    """One gradient-like step of family-weight calibration.

    For each oracle pair (src, target):
      * compute rank of target
      * if rank > 1: for each family, a "lift pressure" = current
        family contribution on this oracle pair MINUS the family's
        average contribution on the top-ranked-but-wrong candidates
      * accumulate lift pressure across all oracle pairs per family
      * apply: ``family_scales[F] *= 1 + eta * normalized_pressure[F]``

    Returns (new_family_scales, mean_rank_residue).
    """
    pressure: Counter = Counter()
    rank_residues: list[int] = []

    for src_qn, target_qn, _cite, _stream in oracle:
        if src_qn not in bitmaps or target_qn not in bitmaps:
            continue
        bm_src = bitmaps[src_qn]
        cands = candidates_for_source.get(src_qn)
        if not cands:
            continue
        rank = predicted_rank(reg, bm_src, cands, target_qn, family_scales)
        rank_residues.append(rank - 1)
        if rank == 1:
            continue  # already correct
        # Compute family contribution on target vs family contribution
        # on the currently-ranked-first candidate
        bm_target = bitmaps[target_qn]
        target_contrib = family_contribution(reg, bm_src, bm_target)
        scored = [
            (qn, score_with_scales(reg, bm_src, bm_cand, family_scales))
            for qn, bm_cand in cands
        ]
        scored.sort(key=lambda x: -x[1])
        top_qn = scored[0][0]
        if top_qn == target_qn:
            continue
        top_contrib = family_contribution(reg, bm_src, bitmaps.get(top_qn, 0))
        # Pressure = boost families firing on target, dampen families
        # firing only on the wrong top
        for fam, w in target_contrib.items():
            pressure[fam] += w
        for fam, w in top_contrib.items():
            pressure[fam] -= w

    # Normalize pressure so scales evolve smoothly
    max_abs = max((abs(v) for v in pressure.values()), default=1.0)
    if max_abs == 0:
        max_abs = 1.0

    new_scales = dict(family_scales)
    for fam, p in pressure.items():
        normed = p / max_abs
        new_scales[fam] = new_scales.get(fam, 1.0) * (1.0 + eta * normed)

    mean_residue = statistics.mean(rank_residues) if rank_residues else 0.0
    return new_scales, mean_residue


# ---------------------------------------------------------------------------
# Calibration loop
# ---------------------------------------------------------------------------


def calibrate(max_iters: int = 8) -> dict:
    repo = Path.cwd()
    paper, agda, python, *_ = load_all(repo)

    agda_docs = _agda_docstring_by_qualname(repo)
    python_docs = _python_docstring_by_qualname(repo)
    paper_rows = [json.loads(l) for l in (repo / "reports" / "paper_decls.jsonl").open()]

    reg = ParallelRegistry()
    all_decls = paper + agda + python
    reg.register_tokens(all_decls, top_n_by_idf=2000)
    reg.register_name_tokens(all_decls)
    reg.register_kinds_and_edges(all_decls)
    reg.register_citations(paper_rows)

    # bitmaps
    bitmaps: dict[str, int] = {}
    for p in paper:
        bitmaps[p.qualname] = reg.fire_bitmap(p, docstring=_paper_doc(paper_rows, p.qualname))
    for a in agda:
        bitmaps[a.qualname] = reg.fire_bitmap(a, docstring=agda_docs.get(a.qualname, ""))
    for y in python:
        bitmaps[y.qualname] = reg.fire_bitmap(y, docstring=python_docs.get(y.qualname, ""))

    # Candidate sets: per agda, all paper decls; per agda, all python decls
    # For efficiency at calibration time we keep only candidates with non-zero
    # initial firing (otherwise rank is identical across all).
    def build_candidates(source_decls, target_decls):
        out: dict[str, list[tuple[str, int]]] = {}
        for s in source_decls:
            hits = []
            for t in target_decls:
                bm = bitmaps.get(t.qualname, 0)
                if bitmaps.get(s.qualname, 0) & bm:
                    hits.append((t.qualname, bm))
            out[s.qualname] = hits
        return out

    agda_paper_cands = build_candidates(agda, paper)
    # Also need python→paper for the python arm of oracle
    python_paper_cands = build_candidates(python, paper)

    # Build oracle
    oracle = build_citation_oracle(paper_rows, agda_docs, python_docs)
    print(f"# oracle size: {len(oracle)} authorial citation pairs", file=sys.stderr)

    # Combine candidate maps for oracle lookup
    cands_by_source = {}
    for k, v in agda_paper_cands.items():
        cands_by_source[k] = v
    for k, v in python_paper_cands.items():
        cands_by_source[k] = v

    # Calibration loop with κ-evolution on plateau
    family_scales: dict[str, float] = {f: 1.0 for f in reg.by_family()}
    trace: list[dict] = []
    prev_residue = float("inf")
    stuck_count = 0
    # Families we've already tried (even if rejected) so we don't propose
    # the same one twice.
    tried_families: set[str] = set()
    # Active extra families: family_tag → fire-check fn
    active_extras: dict = {}

    paper_row_by_qn = {
        f"paper:{r['kind']}:{r.get('label','')}": r
        for r in paper_rows if r.get("label")
    }

    def _recompute_bitmaps():
        """Refresh all decl bitmaps after a new family is registered."""
        for p in paper:
            bitmaps[p.qualname] = reg.fire_bitmap(
                p,
                docstring=_paper_doc(paper_rows, p.qualname),
                extra_families=active_extras,
            )
        for a in agda:
            bitmaps[a.qualname] = reg.fire_bitmap(
                a,
                docstring=agda_docs.get(a.qualname, ""),
                extra_families=active_extras,
            )
        for y in python:
            bitmaps[y.qualname] = reg.fire_bitmap(
                y,
                docstring=python_docs.get(y.qualname, ""),
                extra_families=active_extras,
            )

    def _eval_current(scales) -> tuple[float, float, int]:
        """Evaluate top-1 accuracy + mean rank under ``scales``."""
        ranks: list[int] = []
        top1 = 0
        for src_qn, target_qn, _cite, _stream in oracle:
            if src_qn not in bitmaps or target_qn not in bitmaps:
                continue
            cands = cands_by_source.get(src_qn)
            if not cands:
                continue
            # Rebuild candidate bitmaps (cands still has old bitmap ints,
            # but bitmaps dict has fresh ones).
            fresh_cands = [(qn, bitmaps.get(qn, 0)) for qn, _ in cands]
            rank = predicted_rank(reg, bitmaps[src_qn], fresh_cands, target_qn, scales)
            ranks.append(rank)
            if rank == 1:
                top1 += 1
        if not ranks:
            return 0.0, 0.0, 0
        return statistics.mean(ranks), 100.0 * top1 / len(ranks), len(ranks)

    def _try_candidate_family(
        family_tag: str, items: list[tuple[str, float]], fire_fn, scales
    ) -> tuple[float, int, dict[str, float]]:
        """Register a candidate family + its items, calibrate, measure.

        Per Appendix F's pattern: add the new form, fit its coefficient
        to the residue, then compare.  The (primitive, parameter)
        combinations are generated by
        ``candidate_families.enumerate_candidate_families()``.
        """
        if not items:
            return float("inf"), 0, {}

        n_added = reg.register_candidate_family(family_tag, items)
        if n_added == 0:
            return float("inf"), 0, {}

        active_extras[family_tag] = fire_fn

        _recompute_bitmaps()

        # Rebuild candidate bitmaps (the extra family may now fire on
        # pairs that previously had 0 intersection)
        def rebuild_cands(source_decls, target_decls):
            out = {}
            for s in source_decls:
                hits = []
                for t in target_decls:
                    if bitmaps.get(s.qualname, 0) & bitmaps.get(t.qualname, 0):
                        hits.append((t.qualname, bitmaps[t.qualname]))
                out[s.qualname] = hits
            return out

        # Start the new family at a modest scale (0.5) so it doesn't
        # flood the score space; gradient will pull it toward its
        # proper level.  Other existing scales retained.
        scales_with = dict(scales)
        scales_with[family_tag] = 0.5

        # Run 3 gradient iterations focused on the new family
        # We build a refreshed candidate map that might include pairs
        # newly-connected via the extra family.
        refreshed = rebuild_cands(agda + python, paper)
        # Merge with existing cands_by_source (keep larger candidate sets)
        cands_refreshed = dict(cands_by_source)
        for k, v in refreshed.items():
            if k not in cands_refreshed or len(v) > len(cands_refreshed[k]):
                cands_refreshed[k] = v

        for _ in range(3):
            scales_with, _ = gradient_step(
                reg, oracle, bitmaps, cands_refreshed, scales_with, eta=0.15,
            )

        # Final evaluation under the calibrated scales
        mean_r, top1, _n = _eval_current(scales_with)
        return mean_r, n_added, scales_with

    def _revert_family(family_tag: str):
        """Undo a tentative family registration."""
        reg.drop_family(family_tag)
        active_extras.pop(family_tag, None)
        _recompute_bitmaps()

    for it in range(max_iters):
        # Measure current state
        ranks = []
        top1_hits = 0
        for src_qn, target_qn, _cite, _stream in oracle:
            if src_qn not in bitmaps or target_qn not in bitmaps:
                continue
            cands = cands_by_source.get(src_qn)
            if not cands:
                continue
            rank = predicted_rank(reg, bitmaps[src_qn], cands, target_qn, family_scales)
            ranks.append(rank)
            if rank == 1:
                top1_hits += 1
        mean_r = statistics.mean(ranks) if ranks else 0.0
        median_r = statistics.median(ranks) if ranks else 0.0
        top1_pct = 100 * top1_hits / max(len(ranks), 1)

        print(f"iter {it}: top-1 accuracy = {top1_pct:.1f}%  "
              f"mean_rank = {mean_r:.2f}  median = {median_r}  "
              f"oracle_hits = {len(ranks)}", file=sys.stderr)
        trace.append({
            "iter": it,
            "top1_pct": top1_pct,
            "mean_rank": mean_r,
            "median_rank": median_r,
            "oracle_hits": len(ranks),
            "family_scales": dict(family_scales),
        })

        # Plateau detection
        if abs(prev_residue - mean_r) / max(prev_residue, 1e-6) < 0.02:
            stuck_count += 1
        else:
            stuck_count = 0
        prev_residue = mean_r

        if stuck_count >= 2:
            # κ-evolution: try each candidate family, keep the one
            # that best reduces mean_rank.  This is the Appendix F
            # pattern ``detect_stuck → suggest_kappa_evolution`` but
            # adapted to alignment (discriminator families instead of
            # cost-model parameter forms).
            print(f"# plateau at iter {it}; articulating candidate families", file=sys.stderr)
            baseline = mean_r
            best_family = None
            best_mean = baseline
            best_scales: dict[str, float] | None = None
            per_family_results: dict[str, tuple[float, int]] = {}
            # Enumerate every (primitive, parameter) combination — the
            # specific parameter values are discovered by the loop, not
            # picked by the author.
            for fam_tag, items, fire_fn in candidate_families.enumerate_candidate_families(
                paper + agda + python, paper_rows
            ):
                if fam_tag in tried_families:
                    continue
                if fam_tag in active_extras:
                    continue
                new_mean, n_added, cal_scales = _try_candidate_family(
                    fam_tag, items, fire_fn, family_scales
                )
                per_family_results[fam_tag] = (new_mean, n_added)
                improvement = baseline - new_mean
                print(f"#   candidate {fam_tag!r:28s}  +{n_added} discriminators, "
                      f"mean_rank {baseline:.3f} → {new_mean:.3f} (Δ{improvement:+.3f}) "
                      f"[family_scale={cal_scales.get(fam_tag, 0):.2f}]",
                      file=sys.stderr)
                if new_mean < best_mean - 1e-3:
                    best_family = fam_tag
                    best_mean = new_mean
                    best_scales = cal_scales
                else:
                    _revert_family(fam_tag)
                    tried_families.add(fam_tag)

            if best_family is not None:
                print(f"# κ-evolution: keeping family {best_family!r} "
                      f"(mean_rank {baseline:.3f} → {best_mean:.3f})",
                      file=sys.stderr)
                family_scales = best_scales  # adopt calibrated scales
                stuck_count = 0
                prev_residue = best_mean
                trace[-1]["kappa_evolution"] = {
                    "adopted": best_family,
                    "baseline": baseline,
                    "new_mean": best_mean,
                    "candidates": per_family_results,
                    "adopted_scale": best_scales.get(best_family, 0.0),
                }
            else:
                print(f"# no candidate family improves residue; terminating", file=sys.stderr)
                trace[-1]["kappa_evolution"] = {
                    "adopted": None,
                    "baseline": baseline,
                    "candidates": per_family_results,
                    "verdict": "all candidates rejected",
                }
                break

        # Gradient step
        family_scales, _ = gradient_step(
            reg, oracle, bitmaps, cands_by_source, family_scales, eta=0.15,
        )

    # Write outputs
    reports = repo / "reports"
    (reports / "calibration_trace.jsonl").write_text(
        "\n".join(json.dumps(t) for t in trace) + "\n"
    )
    # Record which candidate families were articulated via κ-evolution,
    # so downstream aligners (align_parallel.py) can register them too.
    evolved_families = [
        f for f in active_extras if f not in {"token", "name_tok", "kind", "edge", "cite"}
    ]
    (reports / "calibrated_weights.json").write_text(
        json.dumps({
            "family_scales": family_scales,
            "registry_size": reg.size(),
            "registry_families": reg.by_family(),
            "oracle_size": len(oracle),
            "final_top1": trace[-1]["top1_pct"] if trace else 0.0,
            "final_mean_rank": trace[-1]["mean_rank"] if trace else 0.0,
            "evolved_families": evolved_families,
        }, indent=2)
    )
    return {"family_scales": family_scales, "trace": trace}


def main():
    result = calibrate(max_iters=10)
    print(json.dumps({
        "family_scales": result["family_scales"],
        "final_top1": result["trace"][-1]["top1_pct"] if result["trace"] else 0,
    }, indent=2))


if __name__ == "__main__":
    main()
