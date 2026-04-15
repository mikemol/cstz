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
| ORDERED_σ (0,1) — Cited | 39 | 41.9% |
| OVER (1,1) — Confirmed | 27 | 29.0% |
| ORDERED_τ (1,0) — Structural | 26 | 28.0% |
| GAP (0,0) — Pending | 1 | 1.1% |

## Signal-presence rates

- Total triples: **93**
- Triples with ≥1 authorial citation: **66** (71.0%) — *this is a LOWER BOUND on correctness per the evidence-semantics principle, not an accuracy measure*
- Average signals per triple: **1.06** / 6 possible

## Signal breakdown

| Signal | Count | % of triples |
|--------|-------|--------------|
| paper_citation_in_agda | 64 | 68.8% |
| paper_citation_in_python | 24 | 25.8% |
| python_name_in_agda | 9 | 9.7% |
| python_path_in_agda | 1 | 1.1% |
| agda_path_in_python | 1 | 1.1% |
