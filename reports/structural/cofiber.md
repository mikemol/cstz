# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

711 Agda decls are not in the committed-triples set.  First 40:

- `agda:module:Univalence`
- `agda:function:exhaustivity-profile`
- `agda:module:BooleanDim`
- `agda:function:class-D-e₂`
- `agda:function:internalHom`
- `agda:postulate:chain-bound`
- `agda:record_field:left-τ`
- `agda:record_field:σ-orient`
- `agda:record_field:regime-incl`
- `agda:record:DiscPair`
- `agda:function:e₁-a₇`
- `agda:module:DeloopCollapse`
- `agda:record_field:cleavage-planes`
- `agda:module:FreeNK`
- `agda:function:monoidal-prod-coeff`
- `agda:record_field:left-point-proj`
- `agda:module:Exhaustivity`
- `agda:function:+V-cancel`
- `agda:function:isBoolean`
- `agda:function:Self-_observe_cell`
- `agda:function:cascade-decomp-adequate`
- `agda:function:a₁`
- `agda:record:FiberedObj`
- `agda:function:overdetΩ`
- `agda:function:Self-_eta_uf-union`
- `agda:function:⊥Ω`
- `agda:function:Self-residue`
- `agda:function:triangle-rot-τ`
- `agda:function:Self-nodes`
- `agda:function:yoneda-A-D`
- `agda:function:wedge-self-zero`
- `agda:function:g0-grade`
- `agda:record_field:obs`
- `agda:function:interchange-profile`
- `agda:function:g3-top-grade`
- `agda:postulate:chain-depth-bound`
- `agda:function:·V-zeroˡ`
- `agda:function:flat-2-merge`
- `agda:function:compose-disjoint`
- `agda:function:Self-rank_distribution`

## Paper-only (no high-confidence Agda or Python match)

112 paper decls are not in the committed-triples set.  First 40:

- `paper:proposition:prop:infinity`
- `paper:definition:def:functor`
- `paper:remark:rem:residue-origins`
- `paper:definition:def:residue`
- `paper:corollary:cor:self-model`
- `paper:definition:def:infinity`
- `paper:definition:def:evolution`
- `paper:theorem:thm:russell`
- `paper:proposition:prop:2morph`
- `paper:definition:def:n-groupoid`
- `paper:remark:rem:interchange-selfhosting`
- `paper:proposition:prop:dynamics-transfer`
- `paper:theorem:thm:subobj`
- `paper:definition:def:complex`
- `paper:proposition:prop:boundary`
- `paper:remark:rem:native-univalence`
- `paper:definition:def:info-order`
- `paper:theorem:thm:self-enrich`
- `paper:definition:def:evidence`
- `paper:theorem:thm:fano`
- `paper:definition:def:composition`
- `paper:remark:rem:interchange-russell`
- `paper:theorem:thm:convergence`
- `paper:definition:def:boolean-dim`
- `paper:definition:def:directed-homotopy`
- `paper:proposition:prop:monoidal`
- `paper:definition:def:eval`
- `paper:theorem:thm:deloop`
- `paper:proposition:prop:fol`
- `paper:definition:def:operationalist`
- `paper:theorem:thm:ext`
- `paper:definition:def:degeneracy`
- `paper:remark:rem:triangle-grounding`
- `paper:theorem:thm:entailed`
- `paper:proposition:prop:symdiff`
- `paper:theorem:thm:nk-free`
- `paper:conjecture:conj:CH`
- `paper:proposition:prop:growth`
- `paper:definition:def:kappa`
- `paper:theorem:thm:sheaf`

## Python-only (no high-confidence Paper or Agda match)

147 Python decls are not in the committed-triples set.  First 40:

- `python:function:morton2`
- `python:function:self_inverse_check`
- `python:function:ext_wedge`
- `python:function:make_bitwise_registry`
- `python:function:_string_kind_tag`
- `python:function:choice_measure`
- `python:function:omega_disj`
- `python:function:dot`
- `python:function:link_vector`
- `python:module:axioms`
- `python:function:_int_bit_seg`
- `python:function:make_category_registry`
- `python:function:make_list_registry`
- `python:function:double_cancel`
- `python:function:verify_fano_line`
- `python:function:make_structural_registry`
- `python:function:check_profile_linearity_exhaustive`
- `python:function:compose_witnesses`
- `python:class:Classifier`
- `python:function:vec_add`
- `python:function:make_int_registry`
- `python:function:_mint_id`
- `python:module:homotopy`
- `python:function:check_cd_commutativity`
- `python:function:_build_int_root`
- `python:function:check_vec_self_inverse`
- `python:function:make_ast_class_registry`
- `python:module:sets`
- `python:function:check_fixed_point_stability`
- `python:function:check_profile_linearity`
- `python:function:ext_boundary`
- `python:module:adapter`
- `python:function:ext_restrict_grade`
- `python:class:ToyBinaryClassifier`
- `python:function:observation_state_to_pff`
- `python:function:check_linear_map_zero`
- `python:module:walker`
- `python:function:make_scalar_kind_registry`
- `python:function:_build_ast_node`
- `python:module:category`
