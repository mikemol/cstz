# Residues: unmatched or ambiguous Agda declarations

337 Agda declarations did not produce a high-confidence triple.
The columns show the top-3 paper/python candidates and why they were rejected
(absolute score below 0.30 or top/second margin below 1.2×).

In Appendix F's terms, each residue here is a four-cell signature:

- **GAP (0,0)**: no token overlap with either side → Agda-only or needs
  a new discriminator that the current basis doesn't include.
- **OVER (1,1)**: multiple candidates tied → ambiguous in current basis;
  residue drilldown into the disagreement point is the κ-evolution step.

| Agda | Missing side(s) | Top paper cand. | Top python cand. |
|------|-----------------|------------------|-------------------|
| module:CSTZ.All | paper | — | function:check_boundary_squa (3.00) |
| module:CSTZ.Axiom.EvalLinearity | python | definition:def:eval-linear (7.00) | function:check_eval_linearit (6.00) |
| module:CSTZ.Axiom.ProfileLinearity | python | definition:def:profile-linea (7.00) | function:check_profile_linea (6.00) |
| module:CSTZ.Category.Adjunction | paper + python | definition:def:category (3.00) | module:category (3.00) |
| record:Adjunction | python | theorem:thm:adjunction (8.27) | — |
| data:Axis | paper + python | corollary:cor:free-fgt (5.56) | — |
| module:CSTZ.Category.Directed | paper + python | definition:def:directed-morp (3.00) | module:category (3.00) |
| module:CSTZ.Category.Emergent | python | definition:def:category (12.56) | module:category (3.00) |
| record:DiscCtx | python | definition:def:category (4.00) | module:pyast (5.27) |
| function:σ-target | python | definition:def:category (4.00) | module:pyast (5.27) |
| function:compose-witnesses | paper | definition:def:category (4.00) | function:compose_witnesses (6.00) |
| module:CSTZ.Category.Functor | paper + python | definition:def:category (3.00) | module:category (3.00) |
| record:DiscFunctor | python | definition:def:functor (3.00) | — |
| function:project | paper + python | — | — |
| function:include | paper + python | — | module:pyast (5.27) |
| module:CSTZ.Category.Limits | paper + python | definition:def:category (3.00) | module:category (3.00) |
| function:equalizerWitness | paper | — | function:equalizer_witness (6.00) |
| module:CSTZ.Category.NatTrans | python | definition:def:category (3.00) | module:category (3.00) |
| record:NatTrans | paper + python | definition:def:nattrans (5.56) | — |
| module:CSTZ.Category.TwoCategory | python | definition:def:category (3.00) | module:category (3.00) |
| function:interchange-at-F | paper | remark:rem:interchange-selfh (3.00) | function:interchange (3.00) |
| module:CSTZ.Category.Yoneda | paper + python | definition:def:category (3.00) | module:category (3.00) |
| function:yoneda-faithful | python | theorem:thm:yoneda (8.56) | — |
| module:CSTZ.Category | python | definition:def:category (3.00) | module:category (3.00) |
| module:CSTZ.Examples.GF2Cubed.Category | python | definition:def:category (3.00) | module:category (3.00) |
| function:compose-e₁-e₂ | python | definition:def:composition (4.00) | function:compose_witnesses (3.00) |
| function:compose-disjoint | paper + python | — | function:compose_witnesses (3.00) |
| function:retract-e₁ | paper + python | theorem:thm:adjunction (5.27) | — |
| function:yoneda-A-B | python | theorem:thm:yoneda (3.00) | — |
| function:yoneda-A-B' | python | theorem:thm:yoneda (3.00) | — |
| function:yoneda-A-C | python | theorem:thm:yoneda (3.00) | — |
| function:yoneda-A-D | python | theorem:thm:yoneda (3.00) | — |
| module:CSTZ.Examples.GF2Cubed.Cycles | python | remark:rem:cycles (3.00) | module:examples (2.00) |
| function:cycle2-link | paper | — | function:link_vector (3.00) |
| function:cycle3-v₁ | paper + python | — | — |
| function:cycle3-v₂ | paper + python | — | — |
| function:cycle3-v₃ | paper + python | — | — |
| function:cycle3-closes | paper + python | — | — |
| function:chain-link | paper + python | — | function:chain_complex_check (3.00) |
| function:chain-cycle-indep | paper + python | remark:rem:cycles (5.27) | function:chain_complex_check (3.00) |
| module:CSTZ.Examples.GF2Cubed.Framework | paper | — | module:framework (3.00) |
| function:profile-lin-check-1 | python | definition:def:profile-linea (7.00) | function:check_profile_linea (6.00) |
| function:profile-lin-check-2 | paper + python | definition:def:profile (3.00) | function:check_profile_linea (6.00) |
| function:residue-a₀-a₂ | paper | definition:def:residue (3.00) | function:is_residue (3.00) |
| function:resolve-a₀-a₂ | paper + python | — | — |
| function:resolve-a₀-a₂' | paper + python | — | — |
| function:order-indep | python | proposition:prop:monoidal (4.00) | — |
| module:CSTZ.Examples.GF2Cubed.Higher | paper | — | module:higher (3.00) |
| function:self-inverse-e₁e₂ | python | theorem:thm:n1cat (4.00) | function:check_vec_self_inve (6.00) |
| function:triangle-check | paper + python | definition:def:triangle (3.00) | function:check_profile_linea (3.00) |
| function:triangle-rot-σ | paper | definition:def:tau-sigma (3.00) | function:triangle_identity (3.00) |
| function:triangle-rot-τ | paper | definition:def:tau-sigma (3.00) | function:triangle_identity (3.00) |
| function:g0-basis | paper + python | — | function:ext_basis (3.00) |
| function:g0-grade | paper + python | — | function:ext_grade (3.00) |
| function:g1-e₁ | paper + python | — | — |
| function:g1-e₂ | paper + python | — | — |
| function:g1-e₃ | paper + python | — | — |
| function:g2-e₁e₂ | paper + python | — | — |
| function:g2-e₁e₃ | paper + python | — | — |
| function:g2-e₂e₃ | paper + python | — | — |
| function:g2-e₁e₂-grade | paper + python | — | function:ext_grade (3.00) |
| function:g2-e₁e₃-grade | paper + python | — | function:ext_grade (3.00) |
| function:g2-e₂e₃-grade | paper + python | — | function:ext_grade (3.00) |
| function:g3-top | paper | — | function:unique_top_form (3.00) |
| function:g3-top-grade | paper + python | — | function:ext_grade (3.00) |
| function:dd-cancels-e₁ | python | proposition:prop:boundary (4.00) | function:check_boundary_squa (4.00) |
| function:dd-cancels-e₂ | paper + python | — | — |
| function:dd-cancels-e₃ | paper + python | — | — |
| function:dd-explicit | paper + python | — | — |
| function:univ-separated | paper + python | — | — |
| function:univ-separated' | paper + python | — | — |
| module:CSTZ.Examples.GF2Cubed.Monoidal | paper | proposition:prop:monoidal (3.00) | module:monoidal (3.00) |
| function:monoidal-prod-coeff | python | definition:def:monoidal-prod (11.56) | function:compose_coeff (3.00) |
| function:assoc-lhs | paper + python | — | — |
| function:assoc-rhs | paper + python | — | — |
| function:strict-assoc | python | theorem:thm:cat-axioms (5.96) | — |
| function:sym-monoidal | python | proposition:prop:sym-monoida (6.00) | module:monoidal (3.00) |
| module:CSTZ.Examples.GF2Cubed.Sets | paper | — | module:sets (3.00) |
| function:ext-a₀≢a₁ | python | theorem:thm:ext (7.00) | function:ext_zero (3.00) |
| function:ext-a₃≢a₅ | python | theorem:thm:ext (3.00) | function:ext_zero (3.00) |
| function:russell-at-zero | python | theorem:thm:russell (7.00) | function:ext_zero (3.00) |
| function:russell-nonlinear | paper | theorem:thm:russell (3.00) | function:russell_exclusion (3.00) |
| function:pair-annihilator-e₁ | paper | — | function:in_annihilator (3.00) |
| function:pair-annihilator-e₃ | paper | — | function:in_annihilator (3.00) |
| function:pair-e₁-agree | paper + python | — | — |
| function:pair-e₃-agree | paper + python | — | — |
| function:pair-separated | paper + python | — | — |
| function:link-v₂ | paper | — | function:link_vector (3.00) |
| function:links-indep | paper + python | — | — |
| function:link-v₃ | paper | — | function:link_vector (3.00) |
| function:symdiff-a₂ | python | proposition:prop:symdiff (12.56) | — |
| function:symdiff-a₆ | python | proposition:prop:symdiff (8.56) | — |
| function:indist-e₁ | python | proposition:prop:infinity (4.00) | — |
| function:indist-e₂ | paper + python | — | — |
| function:indist-diff | paper | — | function:sym_diff_discrimina (3.00) |
| module:CSTZ.Examples.GF2Cubed.Setup | paper + python | — | module:examples (2.00) |
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
| function:eval | paper + python | definition:def:eval-linear (3.00) | function:check_eval_linearit (3.00) |
| function:e₁-a₀ | python | definition:def:discriminator (4.00) | — |
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
| module:CSTZ.Examples.GF2Cubed.Topos | paper | theorem:thm:topos (3.00) | module:topos (3.00) |
| function:classify-inside | paper | remark:rem:cwa-owa (5.56) | function:classify (3.00) |
| function:classify-outside | paper | — | function:classify (3.00) |
| function:fiber-κ₁-size | python | theorem:thm:sheaf (5.27) | function:dim_kappa (3.00) |
| function:fiber-κ₂-size | python | theorem:thm:sheaf (5.27) | function:dim_kappa (3.00) |
| function:fiber-κ₃-size | python | theorem:thm:sheaf (5.27) | function:dim_kappa (3.00) |
| function:conj-overlap-τ | paper | definition:def:tau-sigma (3.00) | function:omega_conj (3.00) |
| function:em-gap | paper + python | — | — |
| function:em-bool | python | proposition:prop:bool-depend (3.00) | — |
| function:dne-check | paper + python | — | function:check_profile_linea (3.00) |
| function:fano-4 | python | theorem:thm:fano (3.00) | function:verify_fano_line (3.00) |
| function:fano-7 | python | theorem:thm:fano (3.00) | function:verify_fano_line (3.00) |
| module:CSTZ.Examples.GF2Cubed | paper + python | — | module:examples (2.00) |
| function:neg-gap | paper | — | function:omega_neg (3.00) |
| function:neg-overlap | paper | — | function:omega_neg (3.00) |
| function:dne-gap | paper | — | function:dne (3.00) |
| function:dne-overlap | paper | — | function:dne (3.00) |
| function:conj-τ-τ | paper | definition:def:tau-sigma (3.00) | function:omega_conj (3.00) |
| function:conj-σ-σ | paper | definition:def:tau-sigma (3.00) | function:omega_conj (3.00) |
| function:conj-gap-any | paper | conjecture:conj:CH (3.00) | function:omega_conj (3.00) |
| function:conj-over-τ | paper | definition:def:tau-sigma (3.00) | function:omega_conj (3.00) |
| function:disj-gap-gap | paper | — | function:omega_disj (3.00) |
| function:em-gap | paper + python | — | — |
| function:em-τ | python | definition:def:tau-sigma (3.00) | — |
| function:em-σ | python | definition:def:tau-sigma (3.00) | — |
| function:em-overlap | paper + python | — | — |
| function:expl-overlap | paper + python | — | module:verification (5.27) |
| function:expl-τ | python | definition:def:tau-sigma (3.00) | module:verification (5.27) |
| … (187 more) | | | |
