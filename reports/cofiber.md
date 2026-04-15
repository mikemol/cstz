# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

673 Agda decls are not in the committed-triples set.  First 40:

- `agda:record:CleavageRuntimeState`
- `agda:function:expl-τ`
- `agda:function:Self-nodes`
- `agda:function:toT`
- `agda:module:Choice`
- `agda:function:e₂+e₃`
- `agda:function:assoc-rhs`
- `agda:module:Symmetric`
- `agda:record_field:canonical-τ`
- `agda:function:+V-comm`
- `agda:function:fano-7`
- `agda:record_field:levels`
- `agda:module:ProofTheory`
- `agda:record_field:map-linear`
- `agda:function:exhaustivity-profile`
- `agda:record_field:line`
- `agda:record:CleavagePlane`
- `agda:function:pairing-via-annihilator`
- `agda:record_field:σ-shrinks`
- `agda:record_field:component`
- `agda:module:Sheaf`
- `agda:function:foundation-profile`
- `agda:function:p₇`
- `agda:module:SPPF`
- `agda:function:a₃`
- `agda:record_field:struct-key`
- `agda:function:η-allη-Name-Self`
- `agda:record_field:universal-unique`
- `agda:function:resolve-a₀-a₂'`
- `agda:function:unknownΩ`
- `agda:function:TechProfile`
- `agda:function:+V-self`
- `agda:function:isDiscriminated`
- `agda:function:cycle3-v₂`
- `agda:function:claim-F`
- `agda:function:kernel-is-subspace`
- `agda:function:·V-linearʳ`
- `agda:record:CleavageLevelState`
- `agda:function:annihilator-to-equality`
- `agda:function:choice-unresolved-S₁`

## Paper-only (no high-confidence Agda or Python match)

90 paper decls are not in the committed-triples set.  First 40:

- `paper:proposition:prop:dynamics-transfer`
- `paper:definition:def:n-groupoid`
- `paper:definition:def:discriminator`
- `paper:definition:def:toroid`
- `paper:theorem:thm:sheaf`
- `paper:definition:def:subobj-class`
- `paper:remark:rem:foundational-status`
- `paper:theorem:thm:groupoid`
- `paper:theorem:thm:cat-axioms`
- `paper:corollary:cor:pro-topos`
- `paper:proposition:prop:infinity`
- `paper:definition:def:monoidal-prod`
- `paper:proposition:prop:naturality`
- `paper:remark:rem:halting`
- `paper:corollary:cor:free-fgt`
- `paper:conjecture:conj:CH`
- `paper:definition:def:tau-sigma`
- `paper:theorem:thm:foundation`
- `paper:definition:def:nattrans`
- `paper:theorem:thm:deloop`
- `paper:proposition:prop:commutative`
- `paper:definition:def:composition`
- `paper:definition:def:boundary`
- `paper:remark:rem:diaconescu`
- `paper:definition:def:limit`
- `paper:theorem:thm:adjunction`
- `paper:definition:def:eval`
- `paper:definition:def:complex`
- `paper:proposition:prop:monotone`
- `paper:definition:def:comprehension`
- `paper:definition:def:fibered`
- `paper:definition:def:membership`
- `paper:remark:rem:cwa-owa`
- `paper:definition:def:representable`
- `paper:corollary:cor:iso-cost`
- `paper:proposition:prop:presheaf-sheaf`
- `paper:remark:rem:2cat`
- `paper:theorem:thm:yoneda`
- `paper:proposition:prop:extremal`
- `paper:definition:def:functor`

## Python-only (no high-confidence Paper or Agda match)

129 Python decls are not in the committed-triples set.  First 40:

- `python:function:chain_depth_bound`
- `python:function:_binarize_fields`
- `python:function:_build_int_bits`
- `python:function:make_category_registry`
- `python:module:walker`
- `python:function:check_cd_commutativity`
- `python:function:gf2_add`
- `python:module:higher`
- `python:function:check_vec_self_inverse`
- `python:function:profile`
- `python:module:projections`
- `python:function:_kind_bucket_for`
- `python:module:homotopy`
- `python:function:_build_ast_node`
- `python:function:ext_add`
- `python:module:pff_json`
- `python:function:check_bilinearity`
- `python:function:check_profile_linearity_exhaustive`
- `python:function:ast_children`
- `python:function:check_boundary_squared_all`
- `python:class:Classifier`
- `python:function:_primitive_kind_subkind`
- `python:function:omega_neg`
- `python:function:basis`
- `python:module:exterior`
- `python:function:morton2`
- `python:function:chi`
- `python:module:classify`
- `python:function:byte_key`
- `python:function:check_bilinear_left`
- `python:function:check_profile_linearity`
- `python:function:_walk_rec`
- `python:function:check_double_cancel`
- `python:function:in_annihilator`
- `python:function:ext_boundary`
- `python:class:ByteClassifier`
- `python:module:category`
- `python:class:AstClassifier`
- `python:function:dne`
- `python:function:make_list_registry`
