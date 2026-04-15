# Residues: unmatched or ambiguous Agda declarations

383 Agda declarations did not produce a high-confidence triple.
The columns show the top-3 paper/python candidates and why they were rejected
(absolute score below 0.30 or top/second margin below 1.2×).

In Appendix F's terms, each residue here is a four-cell signature:

- **GAP (0,0)**: no token overlap with either side → Agda-only or needs
  a new discriminator that the current basis doesn't include.
- **OVER (1,1)**: multiple candidates tied → ambiguous in current basis;
  residue drilldown into the disagreement point is the κ-evolution step.

| Agda | Missing side(s) | Top paper cand. | Top python cand. |
|------|-----------------|------------------|-------------------|
| module:CSTZ.All | paper + python | definition:def:representable (0.32) | function:check_boundary_squa (0.52) |
| module:CSTZ.Axiom.EvalLinearity | paper + python | definition:def:eval (0.45) | function:check_eval_linearit (0.57) |
| module:CSTZ.Axiom.ProfileLinearity | paper + python | definition:def:profile-linea (0.48) | function:check_profile_linea (0.58) |
| module:CSTZ.Category.Adjunction | python | theorem:thm:adjunction (0.45) | function:make_category_regis (0.35) |
| record:Adjunction | python | theorem:thm:adjunction (0.61) | function:check_bilinear_left (0.55) |
| data:Axis | paper + python | definition:def:kappa (0.39) | function:dim_kappa (0.49) |
| module:CSTZ.Category.Directed | paper | definition:def:directed-homo (0.50) | class:DirectedMorphism (0.57) |
| record:DirectedMorphism | paper | definition:def:directed-morp (0.64) | class:DirectedMorphism (0.72) |
| module:CSTZ.Category.Emergent | python | definition:def:category (0.48) | function:make_category_regis (0.35) |
| record:DiscCtx | paper | definition:def:directed-morp (0.47) | function:make_field_registry (0.64) |
| function:σ-target | paper + python | definition:def:eval (0.57) | class:DirectedMorphism (0.57) |
| function:compose-witnesses | paper + python | proposition:prop:2morph (0.40) | function:compose_witnesses (0.70) |
| function:compose-coeff | paper + python | — | function:compose_coeff (0.70) |
| module:CSTZ.Category.Functor | python | definition:def:functor (0.49) | function:make_category_regis (0.35) |
| record:DiscFunctor | python | definition:def:functor (0.66) | function:check_wedge_self_ze (0.48) |
| function:project | python | definition:def:enrichment-da (0.44) | function:gf2_mul (0.48) |
| function:include | python | definition:def:enrichment-da (0.44) | function:gf2_mul (0.48) |
| module:CSTZ.Category.Limits | python | proposition:prop:limits (0.47) | function:make_category_regis (0.35) |
| function:equalizerWitness | paper + python | proposition:prop:2morph (0.40) | function:equalizer_witness (0.75) |
| module:CSTZ.Category.NatTrans | paper + python | definition:def:category (0.30) | function:make_category_regis (0.35) |
| record:NatTrans | paper + python | definition:def:functor (0.47) | module:gf2 (0.45) |
| module:CSTZ.Category.TwoCategory | paper + python | definition:def:category (0.47) | function:make_category_regis (0.51) |
| function:interchange-at-F | paper | remark:rem:interchange-russe (0.61) | function:interchange (0.66) |
| module:CSTZ.Category.Yoneda | python | theorem:thm:yoneda (0.47) | function:make_category_regis (0.35) |
| function:yoneda-faithful | python | theorem:thm:yoneda (0.63) | function:check_eval_linearit (0.46) |
| module:CSTZ.Category | paper + python | definition:def:category (0.47) | function:make_category_regis (0.51) |
| module:CSTZ.Examples.GF2Cubed.Category | paper + python | definition:def:category (0.47) | function:make_category_regis (0.51) |
| function:compose-e₁-e₂ | python | definition:def:evidence (0.37) | function:compose_witnesses (0.63) |
| function:compose-disjoint | paper + python | — | function:compose_witnesses (0.69) |
| function:retract-e₁ | paper + python | theorem:thm:sheaf (0.40) | function:check_eval_linearit (0.47) |
| function:yoneda-A-B | python | theorem:thm:yoneda (0.56) | function:check_eval_linearit (0.46) |
| function:yoneda-A-B' | python | theorem:thm:yoneda (0.56) | function:check_eval_linearit (0.46) |
| function:yoneda-A-C | python | theorem:thm:yoneda (0.56) | function:check_eval_linearit (0.46) |
| function:yoneda-A-D | python | theorem:thm:yoneda (0.56) | function:check_eval_linearit (0.46) |
| module:CSTZ.Examples.GF2Cubed.Cycles | python | remark:rem:cycles (0.44) | function:gf2_mul (0.43) |
| function:cycle3-v₁ | paper + python | — | — |
| function:cycle3-v₂ | paper + python | — | — |
| function:cycle3-v₃ | paper + python | — | — |
| function:cycle3-closes | paper + python | — | — |
| function:chain-link | python | proposition:prop:boundary (0.50) | function:link_vector (0.78) |
| function:chain-cycle-indep | python | proposition:prop:boundary (0.50) | function:chain_depth_bound (0.65) |
| module:CSTZ.Examples.GF2Cubed.Framework | paper + python | corollary:anon_038 (0.33) | module:__init__ (0.50) |
| function:profile-lin-check-1 | paper + python | definition:def:profile-linea (0.59) | function:check_profile_linea (0.68) |
| function:profile-lin-check-2 | paper + python | definition:def:profile-linea (0.59) | function:check_profile_linea (0.68) |
| function:residue-a₀-a₂ | paper | definition:def:residue (0.60) | function:is_residue (0.63) |
| function:resolve-a₀-a₂ | paper + python | proposition:prop:presheaf-sh (0.41) | function:check_eval_linearit (0.46) |
| function:resolve-a₀-a₂' | paper + python | proposition:prop:presheaf-sh (0.41) | function:check_eval_linearit (0.46) |
| function:order-indep | python | definition:def:info-order (0.61) | function:check_eval_linearit (0.46) |
| module:CSTZ.Examples.GF2Cubed.Higher | paper + python | corollary:cor:free-direction (0.31) | module:higher (0.47) |
| function:self-inverse-e₁e₂ | paper + python | corollary:cor:self-model (0.65) | function:check_vec_self_inve (0.66) |
| function:triangle-check | paper + python | definition:def:triangle (0.59) | function:chain_complex_check (0.66) |
| function:triangle-rot-σ | paper | definition:def:triangle (0.59) | function:triangle_identity (0.65) |
| function:triangle-rot-τ | paper | definition:def:triangle (0.59) | function:triangle_identity (0.65) |
| module:CSTZ.Examples.GF2Cubed.Homotopy | python | definition:def:directed-homo (0.50) | module:homotopy (0.51) |
| function:g0-basis | paper + python | definition:def:boundary (0.36) | function:basis (0.67) |
| function:g0-grade | paper + python | remark:anon_099 (0.40) | function:ext_grade (0.71) |
| function:g1-e₁ | paper + python | — | — |
| function:g1-e₂ | paper + python | — | — |
| function:g1-e₃ | paper + python | — | — |
| function:g2-e₁e₂ | python | proposition:prop:forgetful (0.34) | — |
| function:g2-e₁e₃ | python | proposition:prop:forgetful (0.34) | — |
| function:g2-e₂e₃ | python | proposition:prop:forgetful (0.34) | — |
| function:g2-e₁e₂-grade | paper + python | remark:anon_099 (0.41) | function:ext_grade (0.66) |
| function:g2-e₁e₃-grade | paper + python | remark:anon_099 (0.41) | function:ext_grade (0.66) |
| function:g2-e₂e₃-grade | paper + python | remark:anon_099 (0.41) | function:ext_grade (0.66) |
| function:g3-top | paper | theorem:thm:subobj (0.36) | function:unique_top_form (0.65) |
| function:g3-top-grade | paper + python | remark:anon_099 (0.40) | function:unique_top_form (0.67) |
| function:dd-cancels-e₁ | paper + python | — | — |
| function:dd-cancels-e₂ | paper + python | — | — |
| function:dd-cancels-e₃ | paper + python | — | — |
| function:dd-explicit | paper + python | corollary:anon_038 (0.48) | class:StringRoot (0.46) |
| function:comm-subset | paper | proposition:prop:forgetful (0.48) | function:check_wedge_comm (0.65) |
| function:univ-diff | paper | — | function:sym_diff_discrimina (0.70) |
| function:univ-separated | paper + python | proposition:prop:pairing (0.39) | function:check_eval_linearit (0.46) |
| function:univ-separated' | paper + python | proposition:prop:pairing (0.39) | function:check_eval_linearit (0.46) |
| module:CSTZ.Examples.GF2Cubed.Monoidal | python | proposition:prop:sym-monoida (0.56) | module:monoidal (0.48) |
| function:monoidal-prod | paper | proposition:prop:sym-monoida (0.64) | module:monoidal (0.60) |
| function:monoidal-prod-coeff | paper + python | proposition:prop:sym-monoida (0.64) | function:compose_coeff (0.68) |
| function:assoc-lhs | paper + python | — | — |
| function:assoc-rhs | paper + python | — | — |
| function:strict-assoc | python | theorem:thm:cat-axioms (0.45) | — |
| module:CSTZ.Examples.GF2Cubed.Sets | paper + python | remark:anon_041 (0.31) | module:sets (0.46) |
| function:ext-a₀≢a₁ | python | theorem:thm:ext (0.54) | function:ext_grade (0.68) |
| function:ext-a₃≢a₅ | python | theorem:thm:ext (0.54) | function:ext_grade (0.68) |
| function:russell-at-zero | paper + python | remark:rem:interchange-russe (0.57) | function:check_linear_map_ze (0.66) |
| function:russell-nonlinear | paper | remark:rem:interchange-russe (0.60) | function:russell_exclusion (0.61) |
| function:pair-annihilator-e₁ | paper | definition:def:residue (0.44) | function:in_annihilator (0.68) |
| function:pair-annihilator-e₃ | paper | definition:def:residue (0.44) | function:in_annihilator (0.68) |
| function:pair-e₁-agree | paper + python | definition:def:residue (0.44) | function:is_paired (0.48) |
| function:pair-e₃-agree | paper + python | definition:def:residue (0.44) | function:is_paired (0.48) |
| function:pair-separated | paper + python | definition:def:residue (0.44) | function:check_eval_linearit (0.47) |
| function:links-indep | paper + python | — | — |
| function:symdiff-a₂ | python | proposition:prop:symdiff (0.58) | function:check_eval_linearit (0.46) |
| function:symdiff-a₆ | python | proposition:prop:symdiff (0.58) | function:check_eval_linearit (0.46) |
| function:indist-e₁ | paper + python | definition:def:eval (0.40) | function:check_eval_linearit (0.47) |
| function:indist-e₂ | paper + python | definition:def:eval (0.40) | function:check_eval_linearit (0.47) |
| function:indist-diff | paper | — | function:sym_diff_discrimina (0.70) |
| module:CSTZ.Examples.GF2Cubed.Setup | paper + python | — | function:gf2_mul (0.43) |
| function:a₀ | paper + python | — | function:gf2_mul (0.51) |
| function:a₁ | paper + python | — | function:gf2_mul (0.51) |
| function:a₂ | paper + python | — | function:gf2_mul (0.51) |
| function:a₃ | paper + python | — | function:gf2_mul (0.51) |
| function:a₄ | paper + python | — | function:gf2_mul (0.51) |
| function:a₅ | paper + python | — | function:gf2_mul (0.51) |
| function:a₆ | paper + python | — | function:gf2_mul (0.51) |
| function:a₇ | paper + python | — | function:gf2_mul (0.51) |
| function:e₁ | paper + python | — | function:gf2_mul (0.51) |
| function:e₂ | paper + python | — | function:gf2_mul (0.51) |
| function:e₃ | paper + python | — | function:gf2_mul (0.51) |
| function:eval | paper + python | definition:def:eval (0.55) | function:check_eval_linearit (0.63) |
| function:e₁-a₀ | paper + python | definition:def:eval (0.39) | function:check_eval_linearit (0.46) |
| function:e₁-a₄ | paper + python | definition:def:eval (0.39) | function:check_eval_linearit (0.46) |
| function:e₁-a₅ | paper + python | definition:def:eval (0.39) | function:check_eval_linearit (0.46) |
| function:e₁-a₇ | paper + python | definition:def:eval (0.39) | function:check_eval_linearit (0.46) |
| function:e₂-a₂ | paper + python | definition:def:eval (0.39) | function:check_eval_linearit (0.46) |
| function:e₂-a₅ | paper + python | definition:def:eval (0.39) | function:check_eval_linearit (0.46) |
| function:e₃-a₁ | paper + python | definition:def:eval (0.39) | function:check_eval_linearit (0.46) |
| function:e₃-a₄ | paper + python | definition:def:eval (0.39) | function:check_eval_linearit (0.46) |
| function:e₁+e₂ | paper + python | — | function:gf2_mul (0.51) |
| function:e₁+e₃ | paper + python | — | function:gf2_mul (0.51) |
| function:e₂+e₃ | paper + python | — | function:gf2_mul (0.51) |
| function:e₁+e₂+e₃ | paper + python | — | function:gf2_mul (0.51) |
| function:e₁+e₂-val | python | definition:def:evidence (0.36) | function:ext_boundary (0.43) |
| function:e₁+e₂+e₃-val | paper + python | — | function:ext_boundary (0.42) |
| module:CSTZ.Examples.GF2Cubed.Topos | paper + python | corollary:cor:pro-topos (0.50) | module:topos (0.46) |
| function:classify-inside | paper | remark:anon_061 (0.40) | function:classify (0.66) |
| function:classify-outside | paper | remark:anon_061 (0.40) | function:classify (0.66) |
| function:fiber-κ₁-size | python | definition:def:kappa (0.51) | function:dim_kappa (0.64) |
| function:fiber-κ₂-size | python | definition:def:kappa (0.51) | function:dim_kappa (0.64) |
| function:fiber-κ₃-size | python | definition:def:kappa (0.51) | function:dim_kappa (0.64) |
| function:conj-τ-σ | paper + python | definition:def:swap-conj (0.62) | function:omega_conj (0.71) |
| function:conj-overlap-τ | paper + python | definition:def:swap-conj (0.61) | function:omega_conj (0.71) |
| function:em-gap | paper + python | definition:def:info-order (0.48) | function:check_truth_tables (0.48) |
| function:dne-check | paper + python | — | function:dne (0.66) |
| function:fano-1 | python | theorem:thm:fano (0.55) | function:verify_fano_line (0.70) |
| function:fano-4 | python | theorem:thm:fano (0.55) | function:verify_fano_line (0.70) |
| function:fano-7 | python | theorem:thm:fano (0.55) | function:verify_fano_line (0.70) |
| function:galois-order-full | python | definition:def:info-order (0.55) | class:Discriminator (0.39) |
| module:CSTZ.Examples.GF2Cubed | paper + python | — | function:gf2_mul (0.60) |
| module:CSTZ.Examples.TruthTables | paper | remark:rem:proof-assistant (0.27) | function:check_truth_tables (0.54) |
| function:neg-gap | paper | definition:def:info-order (0.46) | function:omega_neg (0.67) |
| function:neg-overlap | paper | definition:def:info-order (0.46) | function:omega_neg (0.67) |
| function:dne-gap | paper | definition:def:info-order (0.47) | function:dne (0.67) |
| function:dne-τ | python | definition:def:tau-sigma (0.59) | function:dne (0.67) |
| function:dne-σ | python | definition:def:tau-sigma (0.59) | function:dne (0.67) |
| function:dne-overlap | paper | definition:def:info-order (0.47) | function:dne (0.67) |
| function:conj-τ-τ | paper + python | definition:def:swap-conj (0.61) | function:omega_conj (0.72) |
| function:conj-τ-σ | paper + python | definition:def:swap-conj (0.62) | function:omega_conj (0.71) |
| function:conj-σ-σ | paper + python | definition:def:swap-conj (0.61) | function:omega_conj (0.72) |
| function:conj-gap-any | paper + python | definition:def:swap-conj (0.61) | function:omega_conj (0.71) |
| … (233 more) | | | |
