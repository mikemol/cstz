# Alignment validation

## Four-cell tier classification

Per Paper §9 Def 9.8 (evidence semantics): a signal firing is
evidence-for; absence of signal is NOT evidence against.  Tiers
below report each committed triple's position in the (τ, σ)
plane where τ = structural name-agreement and σ = authorial
citation in docstrings.  GAP tier is committed-but-pending —
the aligner's score+margin put it in the triple set, but neither
confirmation stream has fired yet.  GAP does not mean wrong.

| Tier | Count | % of triples |
|------|-------|--------------|
| ORDERED_σ (0,1) — Cited | 44 | 43.6% |
| OVER (1,1) — Confirmed | 28 | 27.7% |
| ORDERED_τ (1,0) — Structural | 26 | 25.7% |
| GAP (0,0) — Pending | 3 | 3.0% |

## Signal-presence rates

- Total triples: **101**
- Triples with ≥1 authorial citation: **72** (71.3%) — *this is a LOWER BOUND on correctness per the evidence-semantics principle, not an accuracy measure*
- Average signals per triple: **1.09** / 6 possible

## Signal breakdown

| Signal | Count | % of triples |
|--------|-------|--------------|
| paper_citation_in_agda | 70 | 69.3% |
| paper_citation_in_python | 27 | 26.7% |
| python_name_in_agda | 11 | 10.9% |
| python_path_in_agda | 2 | 2.0% |
