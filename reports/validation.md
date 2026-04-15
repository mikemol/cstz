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
| ORDERED_σ (0,1) — Cited | 75 | 72.8% |
| GAP (0,0) — Pending | 28 | 27.2% |

## Signal-presence rates

- Total triples: **103**
- Triples with ≥1 authorial citation: **75** (72.8%) — *this is a LOWER BOUND on correctness per the evidence-semantics principle, not an accuracy measure*
- Average signals per triple: **1.22** / 6 possible

## Signal breakdown

| Signal | Count | % of triples |
|--------|-------|--------------|
| paper_citation_in_agda | 73 | 70.9% |
| paper_citation_in_python | 33 | 32.0% |
| agda_path_in_python | 10 | 9.7% |
| python_name_in_agda | 9 | 8.7% |
| python_path_in_agda | 1 | 1.0% |
