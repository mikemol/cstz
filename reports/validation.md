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
| GAP (0,0) — Pending | 79 | 45.4% |
| ORDERED_τ (1,0) — Structural | 39 | 22.4% |
| ORDERED_σ (0,1) — Cited | 31 | 17.8% |
| OVER (1,1) — Confirmed | 25 | 14.4% |

## Signal-presence rates

- Total triples: **174**
- Triples with ≥1 authorial citation: **56** (32.2%) — *this is a LOWER BOUND on correctness per the evidence-semantics principle, not an accuracy measure*
- Average signals per triple: **0.47** / 6 possible

## Signal breakdown

| Signal | Count | % of triples |
|--------|-------|--------------|
| paper_citation_in_agda | 35 | 20.1% |
| python_name_in_agda | 26 | 14.9% |
| python_path_in_agda | 10 | 5.7% |
| paper_citation_in_python | 6 | 3.4% |
| agda_path_in_python | 4 | 2.3% |
