# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

639 Agda decls are not in the committed-triples set.  First 40:

- `agda:record_field:unitˡ`
- `agda:function:Self-signature`
- `agda:module:SymDiff`
- `agda:function:Self-_tau_structural_by_child`
- `agda:function:singleton`
- `agda:function:+F-interchange`
- `agda:function:tuple`
- `agda:function:_∨Ω_`
- `agda:function:chain-cycle-indep`
- `agda:function:compose-witnesses`
- `agda:function:Profile`
- `agda:function:witness-from-transition`
- `agda:function:univ-separated`
- `agda:module:TwoCategory`
- `agda:function:e₁`
- `agda:module:Discriminator`
- `agda:function:exhaustivity-profile`
- `agda:module:FOL`
- `agda:function:Self-_parent`
- `agda:function:η-allη-Tuple-tuple`
- `agda:function:_+E_`
- `agda:function:conj-gap-any`
- `agda:function:η-η-cleavage-L0x3ax28x27allη-Constant-strx27x2c_x27allη-Constant-strx27x2c_x27allη-Constant-strx27x29`
- `agda:record_field:from-state`
- `agda:function:load-bearing`
- `agda:function:dd-explicit`
- `agda:record_field:file`
- `agda:function:dne-check`
- `agda:function:classify`
- `agda:function:𝟘`
- `agda:function:Self-find`
- `agda:module:Framework`
- `agda:record_field:ast-type`
- `agda:postulate:operationalist`
- `agda:record_field:commute-right`
- `agda:function:Self-id`
- `agda:record_field:dep-type`
- `agda:function:e₂+e₃`
- `agda:function:σ-idem`
- `agda:function:None`

## Paper-only (no high-confidence Agda or Python match)

66 paper decls are not in the committed-triples set.  First 40:

- `paper:corollary:cor:pro-topos`
- `paper:remark:rem:interchange-selfhosting`
- `paper:theorem:thm:n1cat`
- `paper:proposition:prop:monotone`
- `paper:theorem:thm:self-hosting`
- `paper:corollary:cor:self-model`
- `paper:remark:rem:hyper-recursive`
- `paper:remark:rem:halting`
- `paper:definition:def:evolution`
- `paper:definition:def:residue`
- `paper:definition:def:site`
- `paper:remark:rem:cwa-owa`
- `paper:proposition:prop:forgetful`
- `paper:corollary:cor:iso-cost`
- `paper:definition:def:internal-hom`
- `paper:definition:def:evidence`
- `paper:definition:def:comprehension`
- `paper:remark:rem:foundational-status`
- `paper:proposition:prop:nondefault`
- `paper:proposition:prop:monoidal`
- `paper:definition:def:n-groupoid`
- `paper:proposition:prop:growth`
- `paper:remark:rem:triangle-grounding`
- `paper:definition:def:infinity`
- `paper:proposition:prop:commutative`
- `paper:theorem:thm:adjunction`
- `paper:definition:def:representable`
- `paper:proposition:prop:k-morph`
- `paper:definition:def:functor`
- `paper:proposition:prop:extremal`
- `paper:proposition:prop:bool-dependent`
- `paper:remark:rem:2cat`
- `paper:definition:def:kappa`
- `paper:corollary:cor:free-direction`
- `paper:definition:def:composition`
- `paper:conjecture:conj:CH`
- `paper:proposition:prop:noninvert`
- `paper:remark:rem:residue-origins`
- `paper:proposition:prop:empty`
- `paper:remark:rem:native-univalence`

## Python-only (no high-confidence Paper or Agda match)

114 Python decls are not in the committed-triples set.  First 40:

- `python:class:DiscriminatorRegistry`
- `python:function:tensor_witness`
- `python:function:module_to_tree`
- `python:function:gf2_add`
- `python:module:gf2`
- `python:function:_list_seg`
- `python:function:toy_children`
- `python:function:vec_zero`
- `python:function:check_eval_linearity_exhaustive`
- `python:function:_build_list`
- `python:module:cstz`
- `python:function:ext_is_zero`
- `python:class:Classifier`
- `python:function:check_bilinear_left`
- `python:module:framework`
- `python:function:_fields_seg`
- `python:module:projections`
- `python:function:make_field_registry`
- `python:module:verification`
- `python:function:make_category_registry`
- `python:function:_build_int_bits`
- `python:function:ext_scalar`
- `python:function:check_bilinearity`
- `python:module:observe`
- `python:function:check_boundary_squared_all`
- `python:function:power_set_bound`
- `python:function:make_int_registry`
- `python:function:byte_key`
- `python:class:AstClassifier`
- `python:function:ext_add`
- `python:function:make_string_registry`
- `python:function:verify_fano_line`
- `python:class:ByteClassifier`
- `python:function:_walk_rec`
- `python:function:make_scalar_kind_registry`
- `python:function:_mint_id`
- `python:function:check_fixed_point_stability`
- `python:module:registry`
- `python:function:byte_children`
- `python:function:_int_bit_seg`
