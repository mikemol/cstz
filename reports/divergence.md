# Triples with zero authorial cross-reference evidence

46 out of 57 committed triples have no supporting
signal in the docstrings/comments.  These are the triples most likely
to be wrong — the alignment engine matched them on structural
grounds alone, without the authors ever mentioning the other side.

| agda | paper | python |
|------|-------|--------|
| data:LimitKind | definition:def:limit | class:LimitKind |
| function:class-A-e₁ | definition:def:subobj-class | function:make_ast_class_registry |
| function:class-A-e₂ | definition:def:subobj-class | function:make_ast_class_registry |
| function:class-B-e₁ | definition:def:subobj-class | function:make_ast_class_registry |
| function:class-B-e₂ | definition:def:subobj-class | function:make_ast_class_registry |
| function:class-C-e₁ | definition:def:subobj-class | function:make_ast_class_registry |
| function:class-C-e₂ | definition:def:subobj-class | function:make_ast_class_registry |
| function:class-D-e₁ | definition:def:subobj-class | function:make_ast_class_registry |
| function:class-D-e₂ | definition:def:subobj-class | function:make_ast_class_registry |
| function:cycle2-link | remark:rem:cycles | function:link_vector |
| function:sym-monoidal | proposition:prop:sym-monoidal | function:sym_diff_discriminator |
| function:pairing-diff | proposition:prop:pairing | function:sym_diff_discriminator |
| function:link-v₁ | remark:rem:cycles | function:link_vector |
| function:link-v₂ | remark:rem:cycles | function:link_vector |
| function:link-v₃ | remark:rem:cycles | function:link_vector |
| function:choice-unresolved-S₁ | theorem:thm:choice | function:choice_measure |
| function:choice-unresolved-S₂ | theorem:thm:choice | function:choice_measure |
| function:choice-resolved-S₁ | theorem:thm:choice | function:choice_measure |
| function:choice-resolved-S₂ | theorem:thm:choice | function:choice_measure |
| function:em-bool | proposition:prop:bool-dependent | function:ext_is_zero |
| function:neg-τ | definition:def:tau-sigma | function:omega_neg |
| function:neg-σ | definition:def:tau-sigma | function:omega_neg |
| function:em-τ | definition:def:tau-sigma | function:omega_neg |
| function:em-σ | definition:def:tau-sigma | function:omega_neg |
| function:expl-τ | definition:def:tau-sigma | function:omega_neg |
| function:Subset | proposition:prop:forgetful | function:power_set_bound |
| function:scalar | remark:anon_105 | function:ext_scalar |
| function:disjoint-comm | proposition:prop:forgetful | function:check_wedge_comm |
| function:∪-comm | proposition:prop:forgetful | function:check_wedge_comm |
| module:CSTZ.Framework.FourCell | definition:def:subobj-class | class:CellKind |
| function:evolve | remark:anon_004 | function:evolve |
| module:CSTZ.Higher.Perspectives | proposition:prop:perspectives | module:higher |
| module:CSTZ.Higher.Toroid | definition:def:toroid | module:higher |
| function:chain-complex | proposition:prop:boundary | function:chain_complex_check |
| module:CSTZ.Homotopy.Degeneracy | definition:def:degeneracy | module:homotopy |
| module:CSTZ.Homotopy | definition:def:directed-homotopy | module:homotopy |
| module:CSTZ.Monoidal.Closure | theorem:thm:closure | module:monoidal |
| module:CSTZ.Monoidal.Symmetric | proposition:prop:sym-monoidal | function:sym_diff_discriminator |
| module:CSTZ.Sets.Choice | theorem:thm:choice | function:choice_measure |
| function:finite-choice-terminates | theorem:thm:choice | function:choice_measure |
| module:CSTZ.Sets.SymDiff | proposition:prop:sym-monoidal | function:sym_diff_discriminator |
| module:CSTZ.Topos.Convergence | theorem:thm:convergence | module:topos |
| function:convergence-rate | theorem:thm:convergence | module:topos |
| function:pairing-via-annihilator | proposition:prop:pairing | function:in_annihilator |
| module:CSTZ.Verification.RISC | theorem:thm:topos | function:check_risc |
| function:total-boolean-at-3 | definition:def:boolean-dim | function:is_boolean |
