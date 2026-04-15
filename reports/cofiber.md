# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

668 Agda decls are not in the committed-triples set.  First 40:

- `agda:function:char2`
- `agda:function:dne-gap`
- `agda:module:Regime`
- `agda:record_field:step`
- `agda:record:NatTrans`
- `agda:module:GF2`
- `agda:function:internalHom`
- `agda:record_field:canonical-τ`
- `agda:module:SPPF`
- `agda:function:witness-from-transition`
- `agda:module:CDHexagon`
- `agda:record:TwoTime`
- `agda:function:eqBool`
- `agda:function:σ-sig`
- `agda:function:𝟎E`
- `agda:function:Self-_registry`
- `agda:function:Self-_eta_tower-append`
- `agda:function:Exterior`
- `agda:function:Self-_tau_structural_by_variant-get`
- `agda:record_field:commute-left`
- `agda:record_field:ordered`
- `agda:module:Membership`
- `agda:function:ordered-σ`
- `agda:function:Self-_tau_structural-get`
- `agda:function:symmetry`
- `agda:module:Closure`
- `agda:function:Self-_cascade_abstraction_merge`
- `agda:function:Self-_seed_worklist`
- `agda:module:Wedge`
- `agda:module:FiberedTopos`
- `agda:function:Self-signature`
- `agda:record_field:pullback`
- `agda:function:symdiff-a₆`
- `agda:function:dd-cancels-e₁`
- `agda:module:Groupoid`
- `agda:module:Homotopy`
- `agda:module:ProofTheory`
- `agda:record_field:mono-time`
- `agda:function:ext-a₀≢a₁`
- `agda:function:Self-_eta_abstractions-get`

## Paper-only (no high-confidence Agda or Python match)

90 paper decls are not in the committed-triples set.  First 40:

- `paper:remark:rem:hyper-recursive`
- `paper:theorem:thm:ext`
- `paper:remark:rem:proof-assistant`
- `paper:theorem:thm:subobj`
- `paper:theorem:thm:foundation`
- `paper:proposition:prop:naturality`
- `paper:definition:def:functor`
- `paper:proposition:prop:nondefault`
- `paper:proposition:prop:limits`
- `paper:definition:def:enrichment-data`
- `paper:theorem:thm:self-hosting`
- `paper:definition:def:n-groupoid`
- `paper:remark:rem:triangle-grounding`
- `paper:remark:rem:halting`
- `paper:proposition:prop:presheaf-sheaf`
- `paper:definition:def:fibered`
- `paper:proposition:prop:fol`
- `paper:definition:def:evolution`
- `paper:proposition:prop:dynamics-transfer`
- `paper:remark:rem:interchange-russell`
- `paper:theorem:thm:deloop`
- `paper:remark:rem:diaconescu`
- `paper:proposition:prop:k-morph`
- `paper:definition:def:evidence`
- `paper:proposition:prop:2morph`
- `paper:corollary:cor:iterated-deloop`
- `paper:corollary:cor:pro-topos`
- `paper:theorem:thm:russell`
- `paper:definition:def:boundary`
- `paper:corollary:cor:self-model`
- `paper:example:ex:2morph`
- `paper:theorem:thm:nk-free`
- `paper:definition:def:kappa`
- `paper:theorem:thm:proof-theory`
- `paper:example:ex:banach-tarski`
- `paper:definition:def:complex`
- `paper:remark:rem:2cat`
- `paper:definition:def:infinity`
- `paper:definition:def:internal-hom`
- `paper:proposition:prop:monotone`

## Python-only (no high-confidence Paper or Agda match)

126 Python decls are not in the committed-triples set.  First 40:

- `python:function:check_cd_commutativity`
- `python:function:check_profile_linearity_exhaustive`
- `python:function:_build_ast_node`
- `python:function:check_linear_map_zero`
- `python:function:check_double_cancel`
- `python:function:check_bilinear_left`
- `python:function:walk`
- `python:function:rotate`
- `python:function:_string_kind_tag`
- `python:function:omega_conj`
- `python:function:basis`
- `python:function:ext_add`
- `python:function:parse_to_tree`
- `python:function:byte_key`
- `python:function:make_field_registry`
- `python:class:ToyBinaryClassifier`
- `python:function:check_bilinearity`
- `python:function:omega_disj`
- `python:function:check_eval_linearity`
- `python:function:dim_kappa`
- `python:function:is_residue`
- `python:function:tensor_witness`
- `python:function:ext_wedge`
- `python:function:_walk_rec`
- `python:module:projections`
- `python:class:DiscriminatorRegistry`
- `python:function:ext_grade`
- `python:function:check_vec_self_inverse`
- `python:function:interchange`
- `python:function:_build`
- `python:function:swap_conjugation`
- `python:function:make_toy_registry`
- `python:function:ext_restrict_grade`
- `python:function:exhaustive_filling`
- `python:module:toy`
- `python:module:cstz`
- `python:function:make_category_registry`
- `python:module:registry`
- `python:function:_binarize_fields`
- `python:function:_build_int_bits`
