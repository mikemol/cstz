#!/usr/bin/env python3
"""Gap analysis — find what's MISSING from the triangle.

Per user framing: "the ultimate purpose behind this exercise is to
discover gaps and inconsistencies between the paper, agda and python,
identifying what should be added to each to bring the triangle
identities to completeness."

This script consumes the alignment pipeline's outputs and produces a
classified inventory of the **3×3 cofiber matrix** (presence in each of
the three sources × each of the three possible matchings):

    E/E/E   committed triples (154 at current threshold)
    E/E/M   agda+python aligned, paper missing → formally verified but
            not published
    E/M/E   paper+agda aligned, python missing → theorem lacks runtime
    M/E/E   paper+python aligned, agda missing → impl lacks formal spec
    E/M/M   agda-only → algebraic lemma no paper/python analogue
    M/E/M   paper-only → paper concept not yet formalised or impl'd
    M/M/E   python-only → ad-hoc impl no paper/agda
    (M/M/M impossible by construction — nothing to align)

For each non-trivial cell we produce a ranked report of the "most
actionable" gaps: items with a partial-signal 2-way match but no 3rd
corner.  Those are the places where extending the triangle is
concretely specified.

Output:
  reports/gaps.md     — markdown summary per cell
  reports/gaps.jsonl  — one record per gap, with ranking info

Conflicts (internal inconsistencies) are also surfaced:
  reports/conflicts.md — committed triples where the top/second
                         margin is narrow: multiple paper decls may
                         genuinely correspond to one Agda decl, OR
                         the aligner picked wrong.  Either case is
                         actionable.
"""

from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from align_perspectives import (  # noqa: E402
    load_all, compute_idf, corpus_rarity, pass_1_tokens, normalize_name
)


def _load(path: Path) -> list:
    if not path.exists():
        return []
    return [json.loads(l) for l in path.open() if l.strip()]


def main():
    repo = Path.cwd()
    reports = repo / "reports"

    paper, agda, python, *_ = load_all(repo)
    triples = _load(reports / "triples.jsonl")
    residues = _load(reports / "residues.jsonl")

    matched_paper = {t["paper"] for t in triples}
    matched_agda = {t["agda"] for t in triples}
    matched_python = {t["python"] for t in triples}

    # --- build indexes for quick lookup ---
    paper_by_qn = {p.qualname: p for p in paper}
    agda_by_qn = {a.qualname: a for a in agda}
    python_by_qn = {y.qualname: y for y in python}

    idf = compute_idf(paper + agda + python)

    def score_pair(a, b):
        return pass_1_tokens(a, b, idf)

    # =======================================================================
    # Cell M/E/E: paper+agda aligned but python missing
    # =======================================================================
    # Search over paper×agda pairs with high score that don't have a
    # committed python partner.
    cell_MEE = []  # paper-missing... wait, let me re-read.
    # Convention: the triple-letter code X/Y/Z is (paper/agda/python)
    # with E=explicit (in a committed triple), M=missing.
    #
    #  E/E/M : paper IN triple, agda IN triple, python NOT in triple
    #  E/M/E : paper IN triple, agda NOT in triple, python IN triple
    #  M/E/E : paper NOT in triple, agda IN triple, python IN triple
    #  E/M/M : paper explicit in source, not matched to agda or python
    #  M/E/M : agda explicit in source, not matched
    #  M/M/E : python explicit in source, not matched

    # For each source, what fraction is in a committed triple?
    paper_in = [p for p in paper if p.qualname in matched_paper]
    paper_out = [p for p in paper if p.qualname not in matched_paper]
    agda_in = [a for a in agda if a.qualname in matched_agda]
    agda_out = [a for a in agda if a.qualname not in matched_agda]
    python_in = [y for y in python if y.qualname in matched_python]
    python_out = [y for y in python if y.qualname not in matched_python]

    cell_EEE = len(triples)
    cell_EMM_paper = len(paper_out)  # paper-only (M/M/M impossible, so these are EMM)
    cell_MEM_agda = len(agda_out)
    cell_MME_python = len(python_out)

    # --- Find paper-agda 2-way matches among unmatched paper decls ---
    paper_agda_pairs: list[tuple] = []  # (paper, agda, score)
    for p in paper_out:
        best = (None, 0.0)
        for a in agda:
            s = score_pair(p, a)
            if s > best[1]:
                best = (a, s)
        if best[0] and best[1] >= 0.30:
            paper_agda_pairs.append((p, best[0], best[1]))
    paper_agda_pairs.sort(key=lambda x: -x[2])

    # --- Find paper-python 2-way matches among unmatched paper decls ---
    paper_python_pairs = []
    for p in paper_out:
        best = (None, 0.0)
        for y in python:
            s = score_pair(p, y)
            if s > best[1]:
                best = (y, s)
        if best[0] and best[1] >= 0.30:
            paper_python_pairs.append((p, best[0], best[1]))
    paper_python_pairs.sort(key=lambda x: -x[2])

    # --- Find agda-python 2-way matches among unmatched agda decls ---
    # For each, also check whether there's a PLAUSIBLE paper candidate at
    # a lower (below-alignment-threshold) score.  Those are "near-triples"
    # — items that should have been committed but got kicked to residue
    # by the ambiguity check.  Distinguishing them from TRUE paper gaps
    # (no paper candidate scores above 0.25) is the user's ask.
    agda_python_pairs = []
    near_triples = []
    true_paper_gaps = []
    for a in agda_out:
        best_py = (None, 0.0)
        for y in python:
            s = score_pair(a, y)
            if s > best_py[1]:
                best_py = (y, s)
        if not best_py[0] or best_py[1] < 0.30:
            continue
        # We have an agda+python 2-way match.  Now check the paper side.
        best_p = (None, 0.0)
        for p in paper:
            s = score_pair(a, p)
            if s > best_p[1]:
                best_p = (p, s)
        agda_python_pairs.append((a, best_py[0], best_py[1]))
        if best_p[0] and best_p[1] >= 0.40:
            near_triples.append((a, best_py[0], best_py[1], best_p[0], best_p[1]))
        elif best_p[1] < 0.25:
            true_paper_gaps.append((a, best_py[0], best_py[1], best_p[0] if best_p[0] else None, best_p[1]))
    agda_python_pairs.sort(key=lambda x: -x[2])
    near_triples.sort(key=lambda x: -(x[2] + x[4]))  # rank by combined signal
    true_paper_gaps.sort(key=lambda x: -x[2])

    # =======================================================================
    # Emit reports/gaps.md
    # =======================================================================
    lines = [
        "# Gap analysis — what each side is missing",
        "",
        "This report classifies every named object in paper / agda / python",
        "into its **3×3 cofiber cell** (E=explicit in triple, M=missing).",
        "The interesting cells are the non-EEE ones: they identify concrete",
        "completeness obligations for the paper, for the formalisation, and",
        "for the runtime.",
        "",
        "## Summary",
        "",
        "| Cell | Count | Meaning |",
        "|------|-------|---------|",
        f"| E/E/E | {cell_EEE} | Committed triple: paper+agda+python all present and aligned |",
        f"| E/M/M | {cell_EMM_paper} | Paper object without triple — need agda+python or clearer name |",
        f"| M/E/M | {cell_MEM_agda} | Agda decl without triple — either algebraic lemma (acceptable) or paper needs to state it |",
        f"| M/M/E | {cell_MME_python} | Python object without triple — ad-hoc runtime or classification/observe subsystem |",
        "",
        "## Partial-signal gaps (high value actionable items)",
        "",
        "The rows below are objects NOT in a committed triple that nevertheless",
        "have a high-score 2-way match on one of the other corners — meaning",
        "the third corner is the specific gap.",
        "",
        "### Paper objects with strong Agda match but no Python (E/E/M candidates)",
        "",
        "Paper concepts with a plausible Agda correlate but no Python runtime.",
        "Action: implement these in `src/cstz/`, or document why they are purely",
        "structural (no runtime witness needed).",
        "",
        "| paper | best agda | score |",
        "|-------|-----------|-------|",
    ]
    for p, a, s in paper_agda_pairs[:30]:
        lines.append(f"| {p.qualname.replace('paper:','')[:50]} | {a.qualname.replace('agda:','')[:50]} | {s:.3f} |")
    if len(paper_agda_pairs) > 30:
        lines.append(f"| … ({len(paper_agda_pairs) - 30} more) | | |")

    lines += [
        "",
        "### Paper objects with strong Python match but no Agda (E/M/E candidates)",
        "",
        "Paper concepts realised at runtime but not formally verified.  Action:",
        "add an Agda module or postulate.",
        "",
        "| paper | best python | score |",
        "|-------|-------------|-------|",
    ]
    for p, y, s in paper_python_pairs[:30]:
        lines.append(f"| {p.qualname.replace('paper:','')[:50]} | {y.qualname.replace('python:','')[:50]} | {s:.3f} |")
    if len(paper_python_pairs) > 30:
        lines.append(f"| … ({len(paper_python_pairs) - 30} more) | | |")

    lines += [
        "",
        "### True paper gaps — agda+python present, no plausible paper match (M/E/E)",
        "",
        "Formally specified AND runtime-verified concepts where the paper has",
        "**no** scoring candidate above 0.25.  These are the strongest signals",
        "of genuine paper completeness gaps — the paper truly doesn't name",
        "what Agda and Python both implement.  Action: add a definition or",
        "remark to the paper, or document why the construct is \"internal\"",
        "to the framework.",
        "",
        f"*{len(true_paper_gaps)} items in this bucket.*",
        "",
        "| agda | python (score) | best paper (low score) |",
        "|------|----------------|------------------------|",
    ]
    for a, y, s_y, p_best, s_p in true_paper_gaps[:40]:
        p_str = f"{p_best.qualname.replace('paper:','')[:24]} ({s_p:.2f})" if p_best else "—"
        lines.append(
            f"| {a.qualname.replace('agda:','')[:45]} | {y.qualname.replace('python:','')[:40]} ({s_y:.2f}) | {p_str} |"
        )
    if len(true_paper_gaps) > 40:
        lines.append(f"| … ({len(true_paper_gaps) - 40} more) | | |")

    lines += [
        "",
        "### Near-triples — all three corners have signal but ambiguity blocked commit",
        "",
        "These are items that would be committed triples if the alignment engine",
        "had resolved the ambiguity correctly: agda has a strong python match",
        "AND a plausible paper match (≥0.40).  If a human reviewer agrees with",
        "the paper candidate, these are **alignment-engine failures to recover**,",
        "not gaps.  They are the highest-leverage targets for refining the",
        "alignment pipeline.",
        "",
        f"*{len(near_triples)} items in this bucket.*",
        "",
        "| agda | python | paper | py+paper score |",
        "|------|--------|-------|----------------|",
    ]
    for a, y, s_y, p, s_p in near_triples[:40]:
        combined = s_y + s_p
        lines.append(
            f"| {a.qualname.replace('agda:','')[:40]} | {y.qualname.replace('python:','')[:30]} ({s_y:.2f}) | {p.qualname.replace('paper:','')[:28]} ({s_p:.2f}) | {combined:.2f} |"
        )
    if len(near_triples) > 40:
        lines.append(f"| … ({len(near_triples) - 40} more) | | | |")

    lines += [
        "",
        "## Single-source items (cofiber tips)",
        "",
        "### Paper-only (E/M/M)",
        "",
        f"{len(paper_out)} paper decls have no plausible agda or python match.",
        "Most are likely **remarks** and **examples** that are rhetorical",
        "context rather than formal objects to be mechanised.  First 20:",
        "",
    ]
    # Filter to high-weight paper decls (excluding unlabeled anon_NNN remarks)
    interesting_paper = [p for p in paper_out if not p.name.startswith("<anon")]
    for p in interesting_paper[:20]:
        lines.append(f"- `{p.qualname}`  *{p.kind}*")

    lines += [
        "",
        "### Agda-only (M/E/M)",
        "",
        f"{len(agda_out)} agda decls have no paper/python match.  Many are",
        "low-level algebraic lemmas in GF2/Vec/Exterior — acceptable per",
        "STUDY.md §8.  First 20:",
        "",
    ]
    for a in agda_out[:20]:
        lines.append(f"- `{a.qualname}`  (*{a.kind}*, {a.path})")

    lines += [
        "",
        "### Python-only (M/M/E)",
        "",
        f"{len(python_out)} python decls have no paper/agda match.  Most come",
        "from the `classify/` and `observe.py` subsystems — Python-native",
        "runtime concerns per STUDY.md §8.3.  First 20:",
        "",
    ]
    for y in python_out[:20]:
        lines.append(f"- `{y.qualname}`  (*{y.kind}*, {y.path})")

    (reports / "gaps.md").write_text("\n".join(lines) + "\n")

    # =======================================================================
    # Emit reports/gaps.jsonl (machine-readable)
    # =======================================================================
    with (reports / "gaps.jsonl").open("w") as f:
        for p, a, s in paper_agda_pairs:
            f.write(json.dumps({
                "cell": "E/E/M", "reason": "paper+agda, python missing",
                "paper": p.qualname, "agda": a.qualname, "python": None,
                "score": s,
            }) + "\n")
        for p, y, s in paper_python_pairs:
            f.write(json.dumps({
                "cell": "E/M/E", "reason": "paper+python, agda missing",
                "paper": p.qualname, "agda": None, "python": y.qualname,
                "score": s,
            }) + "\n")
        for a, y, s_y, p_best, s_p in true_paper_gaps:
            f.write(json.dumps({
                "cell": "M/E/E", "reason": "agda+python aligned, paper truly absent",
                "paper": None, "agda": a.qualname, "python": y.qualname,
                "score": s_y,
                "best_paper_attempt": p_best.qualname if p_best else None,
                "best_paper_score": s_p,
            }) + "\n")
        for a, y, s_y, p, s_p in near_triples:
            f.write(json.dumps({
                "cell": "near-triple",
                "reason": "all three have signal but ambiguity blocked commit",
                "paper": p.qualname, "agda": a.qualname, "python": y.qualname,
                "py_score": s_y, "paper_score": s_p, "combined": s_y + s_p,
            }) + "\n")

    # =======================================================================
    # Emit reports/conflicts.md (ambiguous committed triples)
    # =======================================================================
    residue_lines = [
        "# Potential conflicts / ambiguities",
        "",
        "These are cases where the alignment committed a triple but the",
        "second-best candidate scored nearly as high — either the aligner",
        "picked wrong OR there is a genuine ambiguity (the paper states",
        "the concept twice, or the Agda declaration bundles what the paper",
        "splits).  Either case is worth investigating.",
        "",
        "## Residues with tied top candidates",
        "",
        "These are Agda decls that went to residue because no single paper",
        "candidate dominated.  Listing the top-3 candidates lets reviewers",
        "see whether the paper genuinely has redundant material or whether",
        "one of the candidates is a better match than the aligner could tell.",
        "",
        "| Agda | top-3 paper candidates |",
        "|------|-------------------------|",
    ]
    for r in residues[:50]:
        a = r["agda"].replace("agda:", "").replace("|", r"\|")
        pc = r.get("paper_candidates", [])
        if len(pc) < 2:
            continue
        top = pc[0]
        second = pc[1]
        ratio = top[1] / max(second[1], 0.001)
        if ratio > 1.3:
            continue  # not really ambiguous
        cands = " / ".join(
            f"{c[0].replace('paper:','')[:20]} ({c[1]:.2f})"
            for c in pc[:3]
        )
        residue_lines.append(f"| {a[:40]} | {cands} |")

    (reports / "conflicts.md").write_text("\n".join(residue_lines) + "\n")

    # =======================================================================
    # Console summary
    # =======================================================================
    print("Gap analysis summary:")
    print(f"  E/E/E (committed):                 {cell_EEE}")
    print(f"  E/E/M  paper+agda, need python:    {len(paper_agda_pairs)}")
    print(f"  E/M/E  paper+python, need agda:    {len(paper_python_pairs)}")
    print(f"  M/E/E  agda+python, NO paper cand: {len(true_paper_gaps)}")
    print(f"  near-triples (alignment recoverable): {len(near_triples)}")
    print(f"  E/M/M (paper-only):                {len(paper_out)}")
    print(f"  M/E/M (agda-only):                 {len(agda_out)}")
    print(f"  M/M/E (python-only):               {len(python_out)}")
    print(f"\n  wrote: reports/{{gaps,conflicts}}.md, gaps.jsonl")


if __name__ == "__main__":
    main()
