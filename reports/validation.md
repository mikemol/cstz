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
| ORDERED_σ (0,1) — Cited | 46 | 42.2% |
| OVER (1,1) — Confirmed | 36 | 33.0% |
| ORDERED_τ (1,0) — Structural | 26 | 23.9% |
| GAP (0,0) — Pending | 1 | 0.9% |

## Signal-presence rates

- Total triples: **109**
- Triples with ≥1 authorial citation: **82** (75.2%) — *this is a LOWER BOUND on correctness per the evidence-semantics principle, not an accuracy measure*
- Average signals per triple: **1.30** / 6 possible

## Signal breakdown

| Signal | Count | % of triples |
|--------|-------|--------------|
| paper_citation_in_agda | 80 | 73.4% |
| paper_citation_in_python | 38 | 34.9% |
| python_name_in_agda | 11 | 10.1% |
| agda_path_in_python | 10 | 9.2% |
| python_path_in_agda | 3 | 2.8% |
