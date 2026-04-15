# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

648 Agda decls are not in the committed-triples set.  First 40:

- `agda:module:Membership`
- `agda:function:_⊆κ_`
- `agda:function:inAnnihilator`
- `agda:function:monoidal-prod-coeff`
- `agda:module:BooleanDim`
- `agda:function:η-allη-Attribute-Self-_parent`
- `agda:function:chain-link`
- `agda:module:EmptyPairing`
- `agda:function:pair-e₁-agree`
- `agda:function:zero-divisor`
- `agda:function:expl-overlap`
- `agda:function:e₂`
- `agda:function:tuple`
- `agda:function:witness-from-transition`
- `agda:module:Framework`
- `agda:postulate:leibniz`
- `agda:data:CleavageStep`
- `agda:function:links-indep`
- `agda:record:CleavagePlane`
- `agda:function:annihilator-to-equality`
- `agda:record_field:node-id`
- `agda:function:retract-e₁`
- `agda:function:g0-grade`
- `agda:function:p₃`
- `agda:record_field:η-tower`
- `agda:function:·V-zeroʳ`
- `agda:function:interchange-profile`
- `agda:function:face-01-grade`
- `agda:function:claim-F`
- `agda:record:DiscSystem`
- `agda:function:∅`
- `agda:function:link-v₂`
- `agda:function:trans`
- `agda:record:FiberedObj`
- `agda:record_field:keyed-at-level`
- `agda:record_field:mono-time`
- `agda:record_field:right-leg`
- `agda:record:FiberedMor`
- `agda:record_field:component`
- `agda:function:+V-identityˡ`

## Paper-only (no high-confidence Agda or Python match)

70 paper decls are not in the committed-triples set.  First 40:

- `paper:proposition:prop:forgetful`
- `paper:definition:def:boundary`
- `paper:remark:rem:cycles`
- `paper:definition:def:info-order`
- `paper:remark:rem:halting`
- `paper:remark:rem:interchange-selfhosting`
- `paper:theorem:thm:n1cat`
- `paper:remark:rem:triangle-grounding`
- `paper:definition:def:comprehension`
- `paper:remark:rem:residue-origins`
- `paper:conjecture:conj:CH`
- `paper:corollary:cor:free-direction`
- `paper:definition:def:functor`
- `paper:theorem:thm:self-hosting`
- `paper:proposition:prop:2morph`
- `paper:remark:rem:diaconescu`
- `paper:corollary:cor:pro-topos`
- `paper:corollary:cor:self-model`
- `paper:definition:def:swap-conj`
- `paper:definition:def:profile`
- `paper:theorem:thm:cat-axioms`
- `paper:definition:def:powerset`
- `paper:proposition:prop:monoidal`
- `paper:proposition:prop:extremal`
- `paper:definition:def:evidence`
- `paper:remark:rem:interchange-russell`
- `paper:definition:def:eval`
- `paper:definition:def:coverage`
- `paper:proposition:prop:commutative`
- `paper:corollary:cor:free-fgt`
- `paper:theorem:thm:fano`
- `paper:proposition:prop:noninvert`
- `paper:definition:def:kappa`
- `paper:definition:def:evolution`
- `paper:example:ex:banach-tarski`
- `paper:remark:rem:native-univalence`
- `paper:proposition:prop:bool-dependent`
- `paper:example:ex:2morph`
- `paper:definition:def:infinity`
- `paper:proposition:prop:limits`

## Python-only (no high-confidence Paper or Agda match)

115 Python decls are not in the committed-triples set.  First 40:

- `python:function:check_fixed_point_stability`
- `python:function:check_bilinear_right`
- `python:function:make_list_registry`
- `python:function:_build_int_bits`
- `python:function:_walk_rec`
- `python:function:_build_list_item`
- `python:function:make_field_registry`
- `python:function:parse_to_tree`
- `python:function:check_risc`
- `python:function:ext_basis`
- `python:function:ext_add`
- `python:function:bytes_to_tree`
- `python:function:check_double_cancel`
- `python:function:_list_seg`
- `python:function:zpath`
- `python:function:popcount`
- `python:function:_binarize_fields`
- `python:function:walk`
- `python:function:self_inverse_check`
- `python:function:_kind_bucket_for`
- `python:function:verify_fano_line`
- `python:function:check_eval_linearity`
- `python:function:power_set_bound`
- `python:module:adapter`
- `python:function:_build_field`
- `python:function:ast_key`
- `python:function:dot`
- `python:function:check_profile_linearity_exhaustive`
- `python:module:exterior`
- `python:function:ext_is_zero`
- `python:module:observe`
- `python:function:check_boundary_squared_all`
- `python:function:_build_list`
- `python:function:make_bitwise_registry`
- `python:function:make_structural_registry`
- `python:function:_string_kind_tag`
- `python:function:_char_seg`
- `python:module:verification`
- `python:function:chain_depth_bound`
- `python:module:examples`
