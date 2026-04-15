# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

588 Agda decls are not in the committed-triples set.  First 40:

- `agda:record_field:assoc`
- `agda:record_field:map-linear`
- `agda:function:_⊗-coeff_`
- `agda:postulate:exhaustive-filling`
- `agda:function:cycle3-v₂`
- `agda:function:e₁+e₂`
- `agda:function:F`
- `agda:function:T-items`
- `agda:record_field:σ-canon`
- `agda:record:Cell`
- `agda:module:Toroid`
- `agda:function:σ-sig`
- `agda:function:·V-linearˡ`
- `agda:function:Self-_cleavage_ghost_count`
- `agda:function:_∪_`
- `agda:module:Infinity`
- `agda:record_field:sigma`
- `agda:record:IngestPost`
- `agda:function:suc`
- `agda:function:Self-_merge_residue_sets`
- `agda:module:ChainBound`
- `agda:function:Self-node_indices`
- `agda:function:Self-find`
- `agda:function:Self-kappa-_assign`
- `agda:function:groupoid-profile`
- `agda:record_field:left-point`
- `agda:function:Obs`
- `agda:function:idtoeqv`
- `agda:record_field:classRep`
- `agda:data:ℕ`
- `agda:function:Self-_residue_sets`
- `agda:record_field:τ-canon`
- `agda:record_field:level-no`
- `agda:function:Self-id`
- `agda:module:PairingBilinear`
- `agda:function:+F-identity-𝟘ˡ`
- `agda:function:load-bearing`
- `agda:record_field:weight`
- `agda:function:Self-tau-merge`
- `agda:function:compose-e₁-e₂`

## Paper-only (no high-confidence Agda or Python match)

55 paper decls are not in the committed-triples set.  First 40:

- `paper:proposition:prop:monoidal`
- `paper:theorem:thm:subobj`
- `paper:definition:def:representable`
- `paper:definition:def:comprehension`
- `paper:remark:rem:proof-assistant`
- `paper:definition:def:evidence`
- `paper:theorem:thm:self-enrich`
- `paper:theorem:thm:irremovable`
- `paper:definition:def:n-groupoid`
- `paper:definition:def:evolution`
- `paper:remark:rem:diaconescu`
- `paper:proposition:prop:presheaf-sheaf`
- `paper:remark:rem:halting`
- `paper:remark:rem:native-univalence`
- `paper:theorem:thm:ext`
- `paper:proposition:prop:extremal`
- `paper:proposition:prop:noninvert`
- `paper:theorem:thm:entailed`
- `paper:proposition:prop:monotone`
- `paper:theorem:thm:cat-axioms`
- `paper:definition:def:nattrans`
- `paper:proposition:prop:nondefault`
- `paper:remark:rem:foundational-status`
- `paper:proposition:prop:growth`
- `paper:proposition:prop:k-morph`
- `paper:corollary:cor:pro-topos`
- `paper:proposition:prop:empty`
- `paper:definition:def:discriminator`
- `paper:remark:rem:hyper-recursive`
- `paper:proposition:prop:dynamics-transfer`
- `paper:corollary:cor:iso-cost`
- `paper:proposition:prop:fol`
- `paper:theorem:thm:n1cat`
- `paper:corollary:cor:free-direction`
- `paper:example:ex:2morph`
- `paper:definition:def:complex`
- `paper:definition:def:coverage`
- `paper:theorem:thm:deloop`
- `paper:remark:rem:2cat`
- `paper:theorem:thm:exhaustive`

## Python-only (no high-confidence Paper or Agda match)

97 Python decls are not in the committed-triples set.  First 40:

- `python:function:morton2`
- `python:function:_build_list`
- `python:class:ByteClassifier`
- `python:function:check_profile_linearity_exhaustive`
- `python:module:bytes`
- `python:function:check_bilinear_right`
- `python:function:check_double_cancel`
- `python:module:adapter`
- `python:function:check_fixed_point_stability`
- `python:function:make_structural_registry`
- `python:module:cstz`
- `python:function:gf2_add`
- `python:function:ast_children`
- `python:function:make_segment_registry`
- `python:class:ToyBinaryClassifier`
- `python:function:rotate`
- `python:function:make_list_registry`
- `python:function:parse_to_tree`
- `python:function:_build_ast_node`
- `python:function:gf2_mul`
- `python:module:projections`
- `python:module:classify`
- `python:function:toy_children`
- `python:function:_binarize_fields`
- `python:function:_char_seg`
- `python:function:compose_coeff`
- `python:function:make_toy_registry`
- `python:function:popcount`
- `python:function:_kind_bucket_for`
- `python:function:_list_seg`
- `python:module:verification`
- `python:function:_primitive_kind_subkind`
- `python:function:make_category_registry`
- `python:function:ext_restrict_grade`
- `python:function:exhaustive_filling`
- `python:function:ast_key`
- `python:module:walker`
- `python:function:make_string_registry`
- `python:function:double_cancel`
- `python:function:_build_int_bits`
