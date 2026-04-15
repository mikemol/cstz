# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

648 Agda decls are not in the committed-triples set.  First 40:

- `agda:record_field:sigma`
- `agda:record:NatTrans`
- `agda:record:DiscFunctor`
- `agda:module:Degeneracy`
- `agda:function:Self-_recanon_structural_key`
- `agda:function:yoneda-A-D`
- `agda:function:pair-annihilator-e₃`
- `agda:function:Self-_merge_residue_sets`
- `agda:function:dict`
- `agda:function:increment`
- `agda:function:where
    open import Data.Nat using (_<_ ; _≤_ ; z≤n ; s≤s)
    open import Data.Nat.Properties using (≤-refl ; m≤n⇒m≤1+n)

    go`
- `agda:function:float`
- `agda:function:e₂+e₃`
- `agda:function:_+E_`
- `agda:function:self-inverse-morphism`
- `agda:function:Self-tau-merge`
- `agda:record_field:regime`
- `agda:function:+V-self`
- `agda:function:η-allη-Name-tuple`
- `agda:function:Self-_eta_count`
- `agda:function:Self-_eta_abstractions`
- `agda:function:is-real`
- `agda:function:cycle3-v₂`
- `agda:function:triangle-check`
- `agda:record_field:step`
- `agda:data:CellKind`
- `agda:record_field:compose`
- `agda:postulate:merge-canonical-decreases`
- `agda:record:CleavageLevelState`
- `agda:record_field:apex`
- `agda:record:CleavagePlane`
- `agda:function:triangle-rot-τ`
- `agda:function:Self-child_ids`
- `agda:function:·F-idem`
- `agda:function:T-items`
- `agda:module:Delooping`
- `agda:function:_∈S_`
- `agda:function:g1-e₃`
- `agda:module:Discriminator`
- `agda:function:admissible-at-3`

## Paper-only (no high-confidence Agda or Python match)

68 paper decls are not in the committed-triples set.  First 40:

- `paper:corollary:cor:free-fgt`
- `paper:conjecture:conj:CH`
- `paper:definition:def:kappa`
- `paper:proposition:prop:monotone`
- `paper:proposition:prop:empty`
- `paper:definition:def:comprehension`
- `paper:proposition:prop:growth`
- `paper:proposition:prop:dynamics-transfer`
- `paper:definition:def:fibered`
- `paper:remark:rem:hott-paths`
- `paper:remark:rem:halting`
- `paper:remark:rem:proof-assistant`
- `paper:definition:def:nattrans`
- `paper:proposition:prop:presheaf-sheaf`
- `paper:theorem:thm:fano`
- `paper:definition:def:evidence`
- `paper:proposition:prop:limits`
- `paper:corollary:cor:free-direction`
- `paper:proposition:prop:forgetful`
- `paper:corollary:cor:self-model`
- `paper:definition:def:powerset`
- `paper:remark:rem:interchange-selfhosting`
- `paper:proposition:prop:nondefault`
- `paper:definition:def:representable`
- `paper:definition:def:evolution`
- `paper:theorem:thm:adjunction`
- `paper:definition:def:infinity`
- `paper:remark:rem:diaconescu`
- `paper:proposition:prop:perspectives`
- `paper:remark:rem:hyper-recursive`
- `paper:definition:def:composition`
- `paper:remark:rem:2cat`
- `paper:definition:def:coverage`
- `paper:proposition:prop:extremal`
- `paper:proposition:prop:commutative`
- `paper:theorem:thm:yoneda`
- `paper:theorem:thm:n1cat`
- `paper:proposition:prop:monoidal`
- `paper:remark:rem:cwa-owa`
- `paper:theorem:thm:cat-axioms`

## Python-only (no high-confidence Paper or Agda match)

116 Python decls are not in the committed-triples set.  First 40:

- `python:function:make_bitwise_registry`
- `python:function:_primitive_kind_subkind`
- `python:class:DiscriminatorRegistry`
- `python:module:examples`
- `python:function:verify_fano_line`
- `python:function:parse_to_tree`
- `python:function:_list_seg`
- `python:module:registry`
- `python:function:make_list_registry`
- `python:function:_build_ast_node`
- `python:function:observation_state_to_pff`
- `python:function:_fields_seg`
- `python:module:verification`
- `python:function:gf2_mul`
- `python:function:self_inverse_check`
- `python:function:_build`
- `python:function:check_cd_commutativity`
- `python:class:Classifier`
- `python:function:cd_mul`
- `python:function:check_risc`
- `python:module:base`
- `python:function:is_residue`
- `python:function:check_truth_tables`
- `python:function:ext_boundary`
- `python:function:check_vec_self_inverse`
- `python:function:make_int_registry`
- `python:function:interchange`
- `python:module:observe`
- `python:function:popcount`
- `python:function:check_double_cancel`
- `python:function:bytes_to_tree`
- `python:function:walk`
- `python:module:category`
- `python:function:evolve`
- `python:module:bytes`
- `python:function:_string_kind_tag`
- `python:function:_build_char_tree`
- `python:function:ext_grade`
- `python:module:toy`
- `python:function:make_segment_registry`
