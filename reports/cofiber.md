# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

642 Agda decls are not in the committed-triples set.  First 40:

- `agda:function:_·V_`
- `agda:record:Adjunction`
- `agda:module:Graded`
- `agda:function:LinearFunc`
- `agda:function:em-σ`
- `agda:function:+V-assoc`
- `agda:record_field:τ-id`
- `agda:function:isPaired`
- `agda:module:EvalLinearity`
- `agda:record_field:struct-key`
- `agda:function:list`
- `agda:record_field:κ-canon`
- `agda:record_field:Obj`
- `agda:record_field:budget-per-symbol`
- `agda:function:rotate`
- `agda:function:Self-find`
- `agda:postulate:a≡b`
- `agda:function:dd-cancels-e₂`
- `agda:record_field:from-state`
- `agda:record_field:universal-unique`
- `agda:function:Ω`
- `agda:record_field:ordered`
- `agda:function:g1-e₃`
- `agda:function:pair-annihilator-e₁`
- `agda:module:Convergence`
- `agda:function:set`
- `agda:function:isResidueχ`
- `agda:function:internalHom`
- `agda:function:τ-idem`
- `agda:function:boolProject`
- `agda:function:eval`
- `agda:function:toLinear`
- `agda:module:ProfileLinearity`
- `agda:function:grade`
- `agda:function:a₂`
- `agda:function:Self-_resolve`
- `agda:record:DiscSystem`
- `agda:function:Self-name`
- `agda:function:Self-_seed_worklist`
- `agda:function:dict`

## Paper-only (no high-confidence Agda or Python match)

67 paper decls are not in the committed-triples set.  First 40:

- `paper:corollary:cor:free-fgt`
- `paper:definition:def:internal-hom`
- `paper:definition:def:boundary`
- `paper:proposition:prop:growth`
- `paper:proposition:prop:monoidal`
- `paper:remark:rem:triangle-grounding`
- `paper:corollary:cor:free-direction`
- `paper:definition:def:evolution`
- `paper:definition:def:profile-linear`
- `paper:corollary:cor:pro-topos`
- `paper:remark:rem:hyper-recursive`
- `paper:remark:rem:hott-paths`
- `paper:proposition:prop:nondefault`
- `paper:definition:def:fibered`
- `paper:definition:def:info-order`
- `paper:definition:def:coverage`
- `paper:remark:rem:cwa-owa`
- `paper:theorem:thm:yoneda`
- `paper:definition:def:residue`
- `paper:proposition:prop:dynamics-transfer`
- `paper:proposition:prop:k-morph`
- `paper:proposition:prop:limits`
- `paper:definition:def:composition`
- `paper:proposition:prop:commutative`
- `paper:definition:def:site`
- `paper:corollary:cor:truncation-ambiguity`
- `paper:proposition:prop:forgetful`
- `paper:proposition:prop:noninvert`
- `paper:proposition:prop:2morph`
- `paper:remark:rem:cycles`
- `paper:definition:def:n-groupoid`
- `paper:remark:rem:foundational-status`
- `paper:theorem:prop:periodic-2d`
- `paper:definition:def:eval-linear`
- `paper:proposition:prop:bool-dependent`
- `paper:remark:rem:interchange-russell`
- `paper:theorem:thm:n1cat`
- `paper:remark:rem:interchange-selfhosting`
- `paper:theorem:thm:adjunction`
- `paper:definition:def:infinity`

## Python-only (no high-confidence Paper or Agda match)

114 Python decls are not in the committed-triples set.  First 40:

- `python:function:morton2`
- `python:function:parse_to_tree`
- `python:module:pff_json`
- `python:function:module_to_tree`
- `python:function:ext_is_zero`
- `python:function:_build_ast_node`
- `python:function:bytes_to_tree`
- `python:function:_binarize_fields`
- `python:function:is_residue`
- `python:module:bytes`
- `python:function:check_profile_linearity`
- `python:function:ast_children`
- `python:function:popcount`
- `python:function:make_string_registry`
- `python:module:verification`
- `python:function:check_eval_linearity`
- `python:function:_fields_seg`
- `python:function:ext_boundary`
- `python:function:vec_add`
- `python:function:toy_children`
- `python:function:make_toy_registry`
- `python:function:observation_state_to_pff`
- `python:function:check_vec_self_inverse`
- `python:function:ext_grade`
- `python:function:_build_list`
- `python:function:_int_bit_seg`
- `python:function:ext_wedge`
- `python:function:ext_scalar`
- `python:module:projections`
- `python:module:adapter`
- `python:function:_primitive_kind_subkind`
- `python:class:DiscriminatorRegistry`
- `python:function:check_operationalist`
- `python:function:gf2_mul`
- `python:function:check_bilinear_left`
- `python:function:classify`
- `python:function:make_list_registry`
- `python:module:classify`
- `python:function:_build_list_item`
- `python:function:basis`
