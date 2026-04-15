#!/usr/bin/env python3
"""Emit a side-by-side comparison of lexical vs. structural-only modes.

Reads ``reports/calibrated_weights.json`` (lexical) and
``reports/structural/calibrated_weights.json`` (structural), plus their
triples and gap files, and writes ``reports/structural_vs_lexical.md``
summarizing:

    - Registry sizes (how many discriminators each mode exposed)
    - Calibration trajectory (top-1 accuracy, mean rank by iter)
    - Committed triples (tier1 and tier2 counts, citation agreement)
    - Cofiber-cell counts (how many M/E/E etc. each mode detected)
    - Agreement between the two alignments (intersection of triples)

Run after ``bash scripts/run_pipeline.sh`` AND
``bash scripts/run_pipeline.sh --structural`` have both completed.
"""

from __future__ import annotations

import json
from pathlib import Path


def _load_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    return [json.loads(l) for l in path.open() if l.strip()]


def _load_json(path: Path) -> dict:
    if not path.exists():
        return {}
    return json.loads(path.read_text())


def _triple_set(triples: list[dict]) -> set[tuple[str, str, str]]:
    return {(t["agda"], t["paper"], t["python"]) for t in triples}


def main():
    lex = Path("reports")
    st = Path("reports/structural")

    lex_cw = _load_json(lex / "calibrated_weights.json")
    st_cw = _load_json(st / "calibrated_weights.json")

    lex_triples = _load_jsonl(lex / "triples.jsonl")
    st_triples = _load_jsonl(st / "triples.jsonl")

    lex_val = _load_jsonl(lex / "validation.jsonl")
    st_val = _load_jsonl(st / "validation.jsonl")

    lex_gaps = _load_jsonl(lex / "gaps.jsonl")
    st_gaps = _load_jsonl(st / "gaps.jsonl")

    lex_trace = _load_jsonl(lex / "calibration_trace.jsonl")
    st_trace = _load_jsonl(st / "calibration_trace.jsonl")

    def _tier_counts(triples):
        t1 = sum(1 for t in triples if t.get("tier") == "tier1")
        t2 = sum(1 for t in triples if t.get("tier") == "tier2")
        return t1, t2

    def _cited_fraction(triples, val_rows):
        by = {r["agda"]: r for r in val_rows}
        cited = sum(1 for t in triples if by.get(t["agda"], {}).get("n_signals", 0) > 0)
        return cited, len(triples)

    def _gap_counts(gaps):
        from collections import Counter
        c: Counter = Counter(g.get("cell", "?") for g in gaps)
        return dict(c)

    lex_t1, lex_t2 = _tier_counts(lex_triples)
    st_t1, st_t2 = _tier_counts(st_triples)

    lex_cited, lex_total = _cited_fraction(lex_triples, lex_val)
    st_cited, st_total = _cited_fraction(st_triples, st_val)

    lex_g = _gap_counts(lex_gaps)
    st_g = _gap_counts(st_gaps)

    lex_tset = _triple_set(lex_triples)
    st_tset = _triple_set(st_triples)
    both = lex_tset & st_tset
    lex_only = lex_tset - st_tset
    st_only = st_tset - lex_tset

    def _pct(n, d):
        return f"{100*n/max(d,1):.1f}%"

    lines = [
        "# Lexical vs. structural-only alignment comparison",
        "",
        "This report compares two runs of the full pipeline:",
        "",
        "- **Lexical** (default): all discriminator families active",
        "  (`token`, `name_tok`, `cite`, `kind`, `edge`, plus κ-evolved primitives)",
        "- **Structural-only** (`--structural`): lexical families masked;",
        "  only `kind`, `edge`, `subtree_shape`, and residue-driven wedges",
        "",
        "The point of the comparison: if lexical families account for the",
        "bulk of alignment, the paper/agda/python triple is held together",
        "mostly by shared naming conventions.  If structural-only still",
        "delivers substantial agreement, the three sources share real",
        "parse-tree topology for the common concepts.  Per Paper Def 9.8",
        "(evidence semantics), neither mode's 'silence' is evidence",
        "against the triple — they're measurements at different levels.",
        "",
        "## Registry sizes",
        "",
        "| Mode | Total discriminators | Families |",
        "|------|---------------------|----------|",
        f"| Lexical | {lex_cw.get('registry_size', '?')} | {lex_cw.get('registry_families', {})} |",
        f"| Structural | {st_cw.get('registry_size', '?')} | {st_cw.get('registry_families', {})} |",
        "",
        "## Calibration outcomes",
        "",
        "| Mode | Iterations | Final top-1 accuracy | Final mean rank |",
        "|------|-----------|---------------------|----------------|",
        f"| Lexical | {len(lex_trace)} | {lex_cw.get('final_top1', 0):.1f}% | {lex_cw.get('final_mean_rank', 0):.3f} |",
        f"| Structural | {len(st_trace)} | {st_cw.get('final_top1', 0):.1f}% | {st_cw.get('final_mean_rank', 0):.3f} |",
        "",
        "## Committed triples",
        "",
        "| Mode | Tier 1 | Tier 2 | Total | Cited | Citation rate |",
        "|------|--------|--------|-------|-------|---------------|",
        f"| Lexical | {lex_t1} | {lex_t2} | {lex_total} | {lex_cited} | {_pct(lex_cited, lex_total)} |",
        f"| Structural | {st_t1} | {st_t2} | {st_total} | {st_cited} | {_pct(st_cited, st_total)} |",
        "",
        "## Triple-set agreement",
        "",
        "Are the two modes finding the same triples?",
        "",
        "| Partition | Count |",
        "|-----------|-------|",
        f"| Both modes (consensus) | {len(both)} |",
        f"| Lexical-only | {len(lex_only)} |",
        f"| Structural-only | {len(st_only)} |",
        "",
        "**Consensus triples are the highest-confidence subset** — they",
        "are supported by both lexical and structural signal.  Lexical-",
        "only triples rely on shared naming; structural-only triples rely",
        "on parse-tree topology without lexical agreement (these are",
        "interesting because they imply structural match without nominal",
        "agreement, e.g. an Agda record and a Python dataclass that share",
        "field-kind shape but not field names).",
        "",
        "## Cofiber-cell counts",
        "",
        "| Cell | Lexical | Structural |",
        "|------|---------|------------|",
    ]
    for cell in sorted(set(lex_g) | set(st_g)):
        lines.append(f"| {cell} | {lex_g.get(cell, 0)} | {st_g.get(cell, 0)} |")

    lines += [
        "",
        "## Wedge-grade articulation (structural only)",
        "",
    ]
    wedges = st_cw.get("wedge_definitions", [])
    if wedges:
        lines.append(f"Structural mode articulated **{len(wedges)} wedge discriminators** via κ-evolution.")
        from collections import Counter
        grade_counts = Counter(int(w["family"].split("_g")[-1]) for w in wedges if "_g" in w["family"])
        for g, n in sorted(grade_counts.items()):
            lines.append(f"- Grade {g}: {n}")
        lines.append("")
        lines.append("Sample of the top-weighted wedges:")
        lines.append("")
        lines.append("| Grade | Parent A | Parent B | Weight |")
        lines.append("|-------|----------|----------|--------|")
        for w in sorted(wedges, key=lambda x: -x["weight"])[:15]:
            grade = int(w["family"].split("_g")[-1]) if "_g" in w["family"] else "?"
            pa = "/".join(w["parent_a"])[:35]
            pb = "/".join(w["parent_b"])[:35]
            lines.append(f"| {grade} | {pa} | {pb} | {w['weight']:.2f} |")
    else:
        lines.append("(No wedges articulated — calibration terminated without plateau.)")

    lines.append("")
    lines.append("## Sample consensus triples (structural AND lexical agree)")
    lines.append("")
    lines.append("| Agda | Paper | Python |")
    lines.append("|------|-------|--------|")
    for a, p, y in sorted(both)[:20]:
        a_s = a.replace("agda:", "")[:40]
        p_s = p.replace("paper:", "")[:32]
        y_s = y.replace("python:", "")[:30]
        lines.append(f"| {a_s} | {p_s} | {y_s} |")

    if st_only:
        lines.append("")
        lines.append("## Structural-only triples (topology without naming)")
        lines.append("")
        lines.append("| Agda | Paper | Python |")
        lines.append("|------|-------|--------|")
        for a, p, y in sorted(st_only)[:20]:
            a_s = a.replace("agda:", "")[:40]
            p_s = p.replace("paper:", "")[:32]
            y_s = y.replace("python:", "")[:30]
            lines.append(f"| {a_s} | {p_s} | {y_s} |")

    out_path = Path("reports/structural_vs_lexical.md")
    out_path.write_text("\n".join(lines) + "\n")
    print(f"wrote: {out_path}  "
          f"(consensus={len(both)}  lex-only={len(lex_only)}  "
          f"st-only={len(st_only)})")


if __name__ == "__main__":
    main()
