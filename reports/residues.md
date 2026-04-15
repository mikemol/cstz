# Residues: unmatched or ambiguous Agda declarations

347 Agda declarations did not produce a high-confidence triple.
The columns show the top-3 paper/python candidates and why they were rejected
(absolute score below 0.30 or top/second margin below 1.2×).

In Appendix F's terms, each residue here is a four-cell signature:

- **GAP (0,0)**: no token overlap with either side → Agda-only or needs
  a new discriminator that the current basis doesn't include.
- **OVER (1,1)**: multiple candidates tied → ambiguous in current basis;
  residue drilldown into the disagreement point is the κ-evolution step.

| Agda | Missing side(s) | Top paper cand. | Top python cand. |
|------|-----------------|------------------|-------------------|
| module:CSTZ.All | paper + python | — | function:check_boundary_squa (0.73) |
| module:CSTZ.Axiom.EvalLinearity | python | definition:def:eval-linear (5.68) | module:axioms (4.95) |
| module:CSTZ.Axiom.Operationalist | paper | definition:def:operationalis (5.68) | module:axioms (4.95) |
| module:CSTZ.Category.Adjunction | paper + python | definition:def:category (0.73) | module:category (0.73) |
| record:Adjunction | paper + python | theorem:thm:adjunction (3.64) | — |
| data:Axis | python | theorem:thm:sheaf (4.95) | — |
| module:CSTZ.Category.Directed | paper + python | definition:def:directed-morp (0.73) | module:category (0.73) |
| module:CSTZ.Category.Emergent | python | definition:def:category (8.75) | module:category (0.73) |
| record:DiscCtx | python | definition:def:category (4.95) | module:pyast (2.91) |
| function:σ-target | python | definition:def:category (4.95) | module:pyast (2.91) |
| function:compose-witnesses | paper | definition:def:category (4.95) | function:compose_witnesses (4.93) |
| module:CSTZ.Category.Functor | paper + python | definition:def:category (0.73) | module:category (0.73) |
| record:DiscFunctor | paper + python | definition:def:functor (0.73) | — |
| function:project | paper + python | — | — |
| function:include | paper + python | — | module:pyast (2.91) |
| module:CSTZ.Category.Limits | paper + python | definition:def:category (0.73) | module:category (0.73) |
| function:equalizerWitness | paper | — | function:equalizer_witness (4.93) |
| module:CSTZ.Category.NatTrans | paper + python | definition:def:category (0.73) | module:category (0.73) |
| record:NatTrans | paper + python | definition:def:nattrans (3.07) | — |
| module:CSTZ.Category.TwoCategory | paper + python | definition:def:category (0.73) | module:category (0.73) |
| function:interchange-at-F | paper + python | remark:rem:interchange-selfh (0.73) | function:interchange (0.73) |
| module:CSTZ.Category.Yoneda | paper + python | definition:def:category (0.73) | module:category (0.73) |
| function:yoneda-faithful | python | theorem:thm:ext (4.95) | — |
| module:CSTZ.Category | paper + python | definition:def:category (0.73) | module:category (0.73) |
| module:CSTZ.Examples.GF2Cubed.Category | paper + python | definition:def:category (0.73) | module:category (0.73) |
| function:compose-e₁-e₂ | python | definition:def:composition (4.95) | function:compose_witnesses (0.73) |
| function:compose-disjoint | paper + python | — | function:compose_witnesses (0.73) |
| function:retract-e₁ | paper + python | theorem:thm:adjunction (2.91) | — |
| function:yoneda-A-B | paper + python | theorem:thm:yoneda (0.73) | — |
| function:yoneda-A-B' | paper + python | theorem:thm:yoneda (0.73) | — |
| function:yoneda-A-C | paper + python | theorem:thm:yoneda (0.73) | — |
| function:yoneda-A-D | paper + python | theorem:thm:yoneda (0.73) | — |
| module:CSTZ.Examples.GF2Cubed.Cycles | paper + python | remark:rem:cycles (0.73) | module:examples (0.48) |
| function:cycle2-link | paper + python | — | function:link_vector (0.73) |
| function:cycle3-v₁ | paper + python | — | — |
| function:cycle3-v₂ | paper + python | — | — |
| function:cycle3-v₃ | paper + python | — | — |
| function:cycle3-closes | paper + python | — | — |
| function:chain-link | paper + python | — | function:chain_complex_check (0.73) |
| function:chain-cycle-indep | paper + python | remark:rem:cycles (2.91) | function:chain_complex_check (0.73) |
| module:CSTZ.Examples.GF2Cubed.Framework | paper + python | — | module:framework (0.73) |
| function:profile-lin-check-2 | paper + python | definition:def:profile (0.73) | function:check_profile_linea (1.45) |
| function:residue-a₀-a₂ | paper + python | definition:def:residue (0.73) | function:is_residue (0.73) |
| function:resolve-a₀-a₂ | paper + python | — | — |
| function:resolve-a₀-a₂' | paper + python | — | — |
| function:order-indep | python | proposition:prop:monoidal (4.95) | — |
| module:CSTZ.Examples.GF2Cubed.Higher | paper + python | — | module:higher (0.73) |
| function:self-inverse-e₁e₂ | python | theorem:thm:n1cat (4.95) | function:check_vec_self_inve (4.47) |
| function:triangle-check | paper + python | definition:def:triangle (0.73) | function:check_profile_linea (0.73) |
| function:triangle-rot-σ | paper + python | definition:def:tau-sigma (0.73) | function:triangle_identity (0.73) |
| function:triangle-rot-τ | paper + python | definition:def:tau-sigma (0.73) | function:triangle_identity (0.73) |
| function:g0-basis | paper + python | — | function:ext_basis (0.73) |
| function:g0-grade | paper + python | — | function:ext_grade (0.73) |
| function:g1-e₁ | paper + python | — | — |
| function:g1-e₂ | paper + python | — | — |
| function:g1-e₃ | paper + python | — | — |
| function:g2-e₁e₂ | paper + python | — | — |
| function:g2-e₁e₃ | paper + python | — | — |
| function:g2-e₂e₃ | paper + python | — | — |
| function:g2-e₁e₂-grade | paper + python | — | function:ext_grade (0.73) |
| function:g2-e₁e₃-grade | paper + python | — | function:ext_grade (0.73) |
| function:g2-e₂e₃-grade | paper + python | — | function:ext_grade (0.73) |
| function:g3-top | paper + python | — | function:unique_top_form (0.73) |
| function:g3-top-grade | paper + python | — | function:ext_grade (0.73) |
| function:dd-cancels-e₁ | python | proposition:prop:boundary (4.95) | function:check_boundary_squa (4.95) |
| function:dd-cancels-e₂ | paper + python | — | — |
| function:dd-cancels-e₃ | paper + python | — | — |
| function:dd-explicit | paper + python | — | — |
| function:univ-separated | paper + python | — | — |
| function:univ-separated' | paper + python | — | — |
| module:CSTZ.Examples.GF2Cubed.Monoidal | paper + python | proposition:prop:monoidal (0.73) | module:monoidal (0.73) |
| function:monoidal-prod-coeff | python | definition:def:monoidal-prod (7.80) | function:compose_coeff (0.73) |
| function:assoc-lhs | paper + python | — | — |
| function:assoc-rhs | paper + python | — | — |
| function:strict-assoc | python | theorem:thm:cat-axioms (3.30) | — |
| function:sym-monoidal | python | proposition:prop:sym-monoida (4.93) | module:monoidal (0.73) |
| module:CSTZ.Examples.GF2Cubed.Sets | paper + python | — | module:sets (0.73) |
| function:ext-a₀≢a₁ | python | theorem:thm:ext (5.68) | function:ext_zero (0.73) |
| function:ext-a₃≢a₅ | paper + python | theorem:thm:ext (0.73) | function:ext_zero (0.73) |
| function:russell-at-zero | python | theorem:thm:russell (5.68) | function:ext_zero (0.73) |
| function:russell-nonlinear | paper + python | theorem:thm:russell (0.73) | function:russell_exclusion (0.73) |
| function:pair-annihilator-e₁ | paper + python | — | function:in_annihilator (0.73) |
| function:pair-annihilator-e₃ | paper + python | — | function:in_annihilator (0.73) |
| function:pair-e₁-agree | paper + python | — | — |
| function:pair-e₃-agree | paper + python | — | — |
| function:pair-separated | paper + python | — | — |
| function:link-v₂ | paper + python | — | function:link_vector (0.73) |
| function:links-indep | paper + python | — | — |
| function:link-v₃ | paper + python | — | function:link_vector (0.73) |
| function:symdiff-a₂ | python | proposition:prop:symdiff (8.75) | — |
| function:symdiff-a₆ | python | proposition:prop:symdiff (3.80) | — |
| function:indist-e₁ | python | proposition:prop:infinity (4.95) | — |
| function:indist-e₂ | paper + python | — | — |
| function:indist-diff | paper + python | — | function:sym_diff_discrimina (0.73) |
| module:CSTZ.Examples.GF2Cubed.Setup | paper + python | — | module:examples (0.48) |
| function:a₀ | paper + python | — | — |
| function:a₁ | paper + python | — | — |
| function:a₂ | paper + python | — | — |
| function:a₃ | paper + python | — | — |
| function:a₄ | paper + python | — | — |
| function:a₅ | paper + python | — | — |
| function:a₆ | paper + python | — | — |
| function:a₇ | paper + python | — | — |
| function:e₁ | paper + python | — | — |
| function:e₂ | paper + python | — | — |
| function:e₃ | paper + python | — | — |
| function:eval | paper + python | definition:def:eval-linear (0.73) | function:check_eval_linearit (0.73) |
| function:e₁-a₀ | python | definition:def:discriminator (4.95) | — |
| function:e₁-a₄ | paper + python | — | — |
| function:e₁-a₅ | paper + python | — | — |
| function:e₁-a₇ | paper + python | — | — |
| function:e₂-a₂ | paper + python | — | — |
| function:e₂-a₅ | paper + python | — | — |
| function:e₃-a₁ | paper + python | — | — |
| function:e₃-a₄ | paper + python | — | — |
| function:e₁+e₂ | paper + python | — | — |
| function:e₁+e₃ | paper + python | — | — |
| function:e₂+e₃ | paper + python | — | — |
| function:e₁+e₂+e₃ | paper + python | — | — |
| function:e₁+e₂-val | paper + python | — | — |
| function:e₁+e₂+e₃-val | paper + python | — | — |
| module:CSTZ.Examples.GF2Cubed.Topos | paper + python | theorem:thm:topos (0.73) | module:topos (0.73) |
| function:classify-outside | paper + python | — | function:classify (0.73) |
| function:fiber-κ₁-size | python | theorem:thm:topos (4.95) | function:dim_kappa (0.73) |
| function:fiber-κ₂-size | python | theorem:thm:sheaf (2.91) | function:dim_kappa (0.73) |
| function:fiber-κ₃-size | python | theorem:thm:sheaf (2.91) | function:dim_kappa (0.73) |
| function:conj-overlap-τ | paper + python | definition:def:tau-sigma (0.73) | function:omega_conj (0.73) |
| function:em-gap | paper + python | — | — |
| function:em-bool | paper + python | proposition:prop:bool-depend (0.73) | — |
| function:dne-check | paper + python | — | function:check_profile_linea (0.73) |
| function:fano-1 | paper | theorem:thm:fano (5.68) | function:check_fano_lines (10.62) |
| function:fano-4 | paper + python | theorem:thm:fano (0.73) | function:verify_fano_line (0.73) |
| function:fano-7 | paper + python | theorem:thm:fano (0.73) | function:verify_fano_line (0.73) |
| function:galois-order-full | paper | theorem:thm:self-enrich (4.95) | function:check_fano_lines (4.95) |
| module:CSTZ.Examples.GF2Cubed | paper + python | — | module:examples (0.48) |
| function:neg-gap | paper + python | — | function:omega_neg (0.73) |
| function:neg-overlap | paper + python | — | function:omega_neg (0.73) |
| function:dne-gap | paper + python | — | function:dne (0.73) |
| function:dne-overlap | paper + python | — | function:dne (0.73) |
| function:conj-τ-τ | paper + python | definition:def:tau-sigma (0.73) | function:omega_conj (0.73) |
| function:conj-σ-σ | paper + python | definition:def:tau-sigma (0.73) | function:omega_conj (0.73) |
| function:conj-gap-any | paper + python | conjecture:conj:CH (0.73) | function:omega_conj (0.73) |
| function:conj-over-τ | paper + python | definition:def:tau-sigma (0.73) | function:omega_conj (0.73) |
| function:disj-gap-gap | paper + python | — | function:omega_disj (0.73) |
| function:em-gap | paper + python | — | — |
| function:em-τ | paper + python | definition:def:tau-sigma (0.73) | — |
| function:em-σ | paper + python | definition:def:tau-sigma (0.73) | — |
| function:em-overlap | paper + python | — | — |
| function:expl-overlap | paper + python | — | module:verification (2.91) |
| function:expl-τ | paper + python | definition:def:tau-sigma (0.73) | module:verification (2.91) |
| … (197 more) | | | |
