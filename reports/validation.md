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
| ORDERED_σ (0,1) — Cited | 51 | 96.2% |
| GAP (0,0) — Pending | 2 | 3.8% |

## Signal-presence rates

- Total triples: **53**
- Triples with ≥1 authorial citation: **51** (96.2%) — *this is a LOWER BOUND on correctness per the evidence-semantics principle, not an accuracy measure*
- Average signals per triple: **1.96** / 6 possible

## Signal breakdown

| Signal | Count | % of triples |
|--------|-------|--------------|
| paper_citation_in_agda | 50 | 94.3% |
| paper_citation_in_python | 38 | 71.7% |
| agda_path_in_python | 10 | 18.9% |
| python_path_in_agda | 3 | 5.7% |
| python_name_in_agda | 3 | 5.7% |
