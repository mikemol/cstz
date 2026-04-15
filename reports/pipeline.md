# Paper ↔ Agda ↔ Python alignment pipeline

This report is produced by:

1. `scripts/extract_paper.py`  — pandoc LaTeX→JSON AST walker
2. `scripts/extract_agda.py`   — tree-sitter-agda + indent-lexer for Unicode postulates
3. `scripts/extract_python.py` — stdlib `ast` walker
4. `scripts/structural_identity.py` — grammar-reflected wedge-product Id(A), sparse exterior
5. `scripts/align_parallel.py`  — **canonical aligner.**  Uses `ParallelRegistry` (hundreds of discriminators in parallel: IDF tokens, name-tokens, kind discriminators, adjacency-edge discriminators, paper-citation discriminators).  Pair scoring is `weighted_popcount(bitmap_a & bitmap_b)`.  `align_perspectives.py` (legacy 4-pass composite) retained for comparison.
6. `scripts/validate_against_comments.py` — post-hoc authorial-annotation check
7. `scripts/gap_analysis.py` — 3×3 cofiber cell classification, near-triple recovery

No regex runs over source content. No hand-written kind-map. The grammar's
symbol table is the discriminator basis; `cstz.exterior`-style sparse wedge
products compute structural identity; IDF downweights common tokens; residue
drilldown and κ-evolution are inherited from Appendix F of paper2.

## Corpus sizes

| Source | Decl count | Symbol-table (grammar kinds used) |
|--------|------------|-----------------------------------|
| paper  |  158 | ≈28 (pandoc: Header, Div.<env>, Span, Math, Str, …) |
| agda   |  737 | ≈25 (tree-sitter-agda: module, record, data, function, …) |
| python |  453 | ≈73 (`ast.AST` subclasses) |

## Alignment output

- **93** committed triples total
  - Tier 1 (confident, score ≥ 2.0, margin ≥ 1.3×): **31**
  - Tier 2 (plausible, score ≥ 0.5, margin ≥ 1.2×): **62**
- **347** residues (unmatched or ambiguous Agda decls)
- **66** / 93 triples (71.0%) have explicit authorial cross-reference evidence in docstrings/comments

### Evidence signal breakdown

| Signal | Count | % of triples |
|--------|-------|--------------|
| paper_citation_in_agda | 64 | 68.8% |
| paper_citation_in_python | 24 | 25.8% |
| python_name_in_agda | 9 | 9.7% |
| python_path_in_agda | 1 | 1.1% |
| agda_path_in_python | 1 | 1.1% |

## What this demonstrates

The committed triples cluster into the known high-signal modules:
profile-linearity / eval-linearity / operationalist (paper §3), Fano closure,
Russell exclusion, Yoneda, Foundation.  These match STUDY.md §3's postulate
catalog and §2's phase-by-phase correspondence.

The residue population (383) is mostly low-level algebraic lemmas in
`agda/CSTZ/GF2/`, `agda/CSTZ/Vec/`, and `agda/CSTZ/Exterior/` — consistent
with STUDY.md §8's observation that many Agda declarations are structural
sub-steps without a named paper counterpart.  Those fall into the
Agda-E / paper-M / python-I cofiber cells.

## Known limitations (residues from our own loop)

Per Appendix F's own framing, these are κ-evolution targets, not bugs:

1. **Paper-label syntax mismatch.** Authors write `Paper §1, Def 1.1` in
   Agda comments; we extract LaTeX labels like `def:operationalist`.
   The mapping `Def 1.1` ↔ `def:operationalist` requires recovering the
   section-based numbering from pandoc's `Header` hierarchy — feasible but
   not yet done.  Currently `paper_label_in_agda` fires 0 times; it should
   fire on every correct triple.

2. **Name collisions on short Agda modules.**  `CSTZ.All`, `CSTZ.GF2` and
   other re-export/algebra modules match many paper decls at equal token
   overlap.  The `best_or_none` margin check (top ≥ 1.2× second) catches
   these and routes them to residue; a real κ-evolution would drill into
   the module's imports/exports graph to find a finer discriminator.

3. **Grade-2 adjacency is coarse cross-source.**  We compare adjacency
   cardinality and density but not per-edge kind alignment — that would
   require the emergent role map to be refined to field-edge granularity.

