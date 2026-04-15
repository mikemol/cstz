# Residues: unmatched or ambiguous Agda declarations

387 Agda declarations did not produce a high-confidence triple.
The columns show the top-3 paper/python candidates and why they were rejected
(absolute score below 0.30 or top/second margin below 1.2×).

In Appendix F's terms, each residue here is a four-cell signature:

- **GAP (0,0)**: no token overlap with either side → Agda-only or needs
  a new discriminator that the current basis doesn't include.
- **OVER (1,1)**: multiple candidates tied → ambiguous in current basis;
  residue drilldown into the disagreement point is the κ-evolution step.

| Agda | Missing side(s) | Top paper cand. | Top python cand. |
|------|-----------------|------------------|-------------------|
| module:CSTZ.All | paper + python | — | function:check_boundary_squa (1.64) |
| module:CSTZ.Category.Adjunction | paper + python | definition:def:category (1.64) | module:category (1.64) |
| record:Adjunction | python | theorem:thm:adjunction (5.14) | — |
| data:Axis | python | theorem:thm:sheaf (4.88) | — |
| module:CSTZ.Category.Directed | paper + python | definition:def:directed-morp (1.64) | module:category (1.64) |
| module:CSTZ.Category.Emergent | python | definition:def:category (10.20) | module:category (1.64) |
| record:DiscCtx | python | definition:def:category (4.88) | module:pyast (3.50) |
| function:σ-target | python | definition:def:category (4.88) | module:pyast (3.50) |
| function:compose-witnesses | paper | definition:def:category (4.88) | function:compose_witnesses (3.28) |
| module:CSTZ.Category.Functor | paper + python | definition:def:category (1.64) | module:category (1.64) |
| record:DiscFunctor | paper + python | definition:def:functor (1.64) | — |
| function:project | paper + python | — | — |
| function:include | paper + python | — | module:pyast (3.50) |
| module:CSTZ.Category.Limits | paper + python | definition:def:category (1.64) | module:category (1.64) |
| data:LimitKind | paper | definition:def:limit (1.64) | class:LimitKind (3.28) |
| function:equalizerWitness | paper | — | function:equalizer_witness (3.28) |
| module:CSTZ.Category.NatTrans | paper + python | definition:def:category (1.64) | module:category (1.64) |
| record:NatTrans | paper + python | definition:def:nattrans (3.69) | — |
| module:CSTZ.Category.TwoCategory | paper + python | definition:def:category (1.64) | module:category (1.64) |
| function:interchange-at-F | paper + python | remark:rem:interchange-selfh (1.64) | function:interchange (1.64) |
| module:CSTZ.Category.Yoneda | paper + python | definition:def:category (1.64) | module:category (1.64) |
| function:yoneda-faithful | paper + python | theorem:thm:yoneda (5.33) | — |
| module:CSTZ.Category | paper + python | definition:def:category (1.64) | module:category (1.64) |
| module:CSTZ.Examples.GF2Cubed.Category | paper + python | definition:def:category (1.64) | module:category (1.64) |
| function:class-A-e₁ | python | definition:def:category (4.88) | function:make_ast_class_regi (1.64) |
| function:class-A-e₂ | paper + python | definition:def:subobj-class (1.64) | function:make_ast_class_regi (1.64) |
| function:class-B-e₁ | paper + python | definition:def:subobj-class (1.64) | function:make_ast_class_regi (1.64) |
| function:class-B-e₂ | paper + python | definition:def:subobj-class (1.64) | function:make_ast_class_regi (1.64) |
| function:class-C-e₁ | paper + python | definition:def:subobj-class (1.64) | function:make_ast_class_regi (1.64) |
| function:class-C-e₂ | paper + python | definition:def:subobj-class (1.64) | function:make_ast_class_regi (1.64) |
| function:class-D-e₁ | paper + python | definition:def:subobj-class (1.64) | function:make_ast_class_regi (1.64) |
| function:class-D-e₂ | paper + python | definition:def:subobj-class (1.64) | function:make_ast_class_regi (1.64) |
| function:compose-e₁-e₂ | python | definition:def:composition (4.88) | function:compose_witnesses (1.64) |
| function:compose-disjoint | paper + python | — | function:compose_witnesses (1.64) |
| function:retract-e₁ | paper + python | theorem:thm:adjunction (3.50) | — |
| function:yoneda-A-B | paper + python | theorem:thm:yoneda (1.64) | — |
| function:yoneda-A-B' | paper + python | theorem:thm:yoneda (1.64) | — |
| function:yoneda-A-C | paper + python | theorem:thm:yoneda (1.64) | — |
| function:yoneda-A-D | paper + python | theorem:thm:yoneda (1.64) | — |
| module:CSTZ.Examples.GF2Cubed.Cycles | paper + python | remark:rem:cycles (1.64) | module:examples (1.09) |
| function:cycle2-link | paper + python | — | function:link_vector (1.64) |
| function:cycle3-v₁ | paper + python | — | — |
| function:cycle3-v₂ | paper + python | — | — |
| function:cycle3-v₃ | paper + python | — | — |
| function:cycle3-closes | paper + python | — | — |
| function:chain-link | paper + python | — | function:chain_complex_check (1.64) |
| function:chain-cycle-indep | paper + python | remark:rem:cycles (3.50) | function:chain_complex_check (1.64) |
| module:CSTZ.Examples.GF2Cubed.Framework | paper + python | — | module:framework (1.64) |
| function:profile-lin-check-2 | paper + python | definition:def:profile (1.64) | function:check_profile_linea (3.28) |
| function:residue-a₀-a₂ | paper + python | definition:def:residue (1.64) | function:is_residue (1.64) |
| function:resolve-a₀-a₂ | paper + python | — | — |
| function:resolve-a₀-a₂' | paper + python | — | — |
| function:order-indep | python | proposition:prop:monoidal (4.88) | — |
| module:CSTZ.Examples.GF2Cubed.Higher | paper + python | — | module:higher (1.64) |
| function:self-inverse-e₁e₂ | python | theorem:thm:n1cat (4.88) | function:check_vec_self_inve (3.28) |
| function:triangle-check | paper + python | definition:def:triangle (1.64) | function:check_profile_linea (1.64) |
| function:triangle-rot-σ | paper + python | definition:def:tau-sigma (1.64) | function:triangle_identity (1.64) |
| function:triangle-rot-τ | paper + python | definition:def:tau-sigma (1.64) | function:triangle_identity (1.64) |
| module:CSTZ.Examples.GF2Cubed.Homotopy | paper + python | definition:def:directed-homo (1.64) | module:homotopy (1.64) |
| function:g0-basis | paper + python | — | function:ext_basis (1.64) |
| function:g0-grade | paper + python | — | function:ext_grade (1.64) |
| function:g1-e₁ | paper + python | — | — |
| function:g1-e₂ | paper + python | — | — |
| function:g1-e₃ | paper + python | — | — |
| function:g2-e₁e₂ | paper + python | — | — |
| function:g2-e₁e₃ | paper + python | — | — |
| function:g2-e₂e₃ | paper + python | — | — |
| function:g2-e₁e₂-grade | paper + python | — | function:ext_grade (1.64) |
| function:g2-e₁e₃-grade | paper + python | — | function:ext_grade (1.64) |
| function:g2-e₂e₃-grade | paper + python | — | function:ext_grade (1.64) |
| function:g3-top | paper + python | — | function:unique_top_form (1.64) |
| function:g3-top-grade | paper + python | — | function:ext_grade (1.64) |
| function:dd-cancels-e₁ | python | proposition:prop:boundary (4.88) | function:check_boundary_squa (4.88) |
| function:dd-cancels-e₂ | paper + python | — | — |
| function:dd-cancels-e₃ | paper + python | — | — |
| function:dd-explicit | paper + python | — | — |
| function:comm-subset | python | theorem:thm:groupoid (4.88) | function:check_wedge_comm (1.64) |
| function:univ-diff | python | proposition:prop:univalence (4.88) | function:sym_diff_discrimina (1.64) |
| function:univ-separated | paper + python | — | — |
| function:univ-separated' | paper + python | — | — |
| module:CSTZ.Examples.GF2Cubed.Monoidal | paper + python | proposition:prop:monoidal (1.64) | module:monoidal (1.64) |
| function:monoidal-prod | python | definition:def:monoidal-prod (11.84) | module:monoidal (1.64) |
| function:monoidal-prod-coeff | python | definition:def:monoidal-prod (6.97) | function:compose_coeff (1.64) |
| function:assoc-lhs | paper + python | — | — |
| function:assoc-rhs | paper + python | — | — |
| function:strict-assoc | python | theorem:thm:cat-axioms (3.96) | — |
| function:sym-monoidal | python | proposition:prop:sym-monoida (3.28) | module:monoidal (1.64) |
| module:CSTZ.Examples.GF2Cubed.Sets | paper + python | — | module:sets (1.64) |
| function:ext-a₀≢a₁ | python | theorem:thm:ext (6.51) | function:ext_zero (1.64) |
| function:ext-a₃≢a₅ | paper + python | theorem:thm:ext (1.64) | function:ext_zero (1.64) |
| function:russell-at-zero | python | theorem:thm:russell (6.51) | function:ext_zero (1.64) |
| function:russell-nonlinear | paper + python | theorem:thm:russell (1.64) | function:russell_exclusion (1.64) |
| function:pairing-diff | python | proposition:prop:pairing (6.51) | function:sym_diff_discrimina (1.64) |
| function:pair-annihilator-e₁ | paper + python | — | function:in_annihilator (1.64) |
| function:pair-annihilator-e₃ | paper + python | — | function:in_annihilator (1.64) |
| function:pair-e₁-agree | paper + python | — | — |
| function:pair-e₃-agree | paper + python | — | — |
| function:pair-separated | paper + python | — | — |
| function:link-v₁ | python | theorem:thm:foundation (4.88) | function:link_vector (1.64) |
| function:link-v₂ | paper + python | — | function:link_vector (1.64) |
| function:links-indep | paper + python | — | — |
| function:link-v₃ | paper + python | — | function:link_vector (1.64) |
| function:choice-unresolved-S₁ | python | theorem:thm:choice (6.51) | function:choice_measure (1.64) |
| function:choice-unresolved-S₂ | paper + python | theorem:thm:choice (1.64) | function:choice_measure (1.64) |
| function:choice-resolved-S₁ | paper + python | theorem:thm:choice (1.64) | function:choice_measure (1.64) |
| function:choice-resolved-S₂ | paper + python | theorem:thm:choice (1.64) | function:choice_measure (1.64) |
| function:symdiff-a₂ | python | proposition:prop:symdiff (10.20) | — |
| function:symdiff-a₆ | python | proposition:prop:symdiff (5.33) | — |
| function:indist-e₁ | python | proposition:prop:infinity (4.88) | — |
| function:indist-e₂ | paper + python | — | — |
| function:indist-diff | paper + python | — | function:sym_diff_discrimina (1.64) |
| module:CSTZ.Examples.GF2Cubed.Setup | paper + python | — | module:examples (1.09) |
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
| function:eval | paper + python | definition:def:eval-linear (1.64) | function:check_eval_linearit (1.64) |
| function:e₁-a₀ | python | definition:def:discriminator (4.88) | — |
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
| module:CSTZ.Examples.GF2Cubed.Topos | paper + python | theorem:thm:topos (1.64) | module:topos (1.64) |
| function:classify-inside | python | theorem:thm:subobj (4.88) | function:classify (1.64) |
| function:classify-outside | paper + python | — | function:classify (1.64) |
| function:fiber-κ₁-size | python | theorem:thm:topos (4.88) | function:dim_kappa (1.64) |
| function:fiber-κ₂-size | python | theorem:thm:sheaf (3.50) | function:dim_kappa (1.64) |
| function:fiber-κ₃-size | python | theorem:thm:sheaf (3.50) | function:dim_kappa (1.64) |
| function:conj-τ-σ | python | definition:def:tau-sigma (3.28) | function:omega_conj (1.64) |
| function:conj-overlap-τ | paper + python | definition:def:tau-sigma (1.64) | function:omega_conj (1.64) |
| function:em-gap | paper + python | — | — |
| function:em-bool | paper + python | proposition:prop:bool-depend (1.64) | — |
| function:dne-check | paper + python | — | function:check_profile_linea (1.64) |
| function:fano-4 | paper + python | theorem:thm:fano (1.64) | function:verify_fano_line (1.64) |
| … (237 more) | | | |
