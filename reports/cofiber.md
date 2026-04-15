# Cofiber — objects named on one side but missing on others

Per STUDY.md §8, the cofibration classifies each concept into one of nine
E/I/M × E/I/M cells.  The alignment loop above directly populates the
E/E/E cell (committed triples).  Here we enumerate the single-sided rows
— concepts **E**xplicit on one source and **M**issing on (at least) one
other.

## Agda-only (no high-confidence paper or python match)

649 Agda decls are not in the committed-triples set.  First 40:

- `agda:function:Self-_tau_structural`
- `agda:function:wedge₂-comm`
- `agda:function:Self-_parent`
- `agda:function:a₀`
- `agda:function:disj-gap-gap`
- `agda:module:NatTrans`
- `agda:function:_⟨_⟩`
- `agda:module:ProofTheory`
- `agda:postulate:merge-canonical-decreases`
- `agda:function:κ-idem`
- `agda:record_field:mapDisc`
- `agda:function:_·V_`
- `agda:function:em-σ`
- `agda:function:float`
- `agda:record:IngestPre`
- `agda:function:τ-idem`
- `agda:record:PullbackWitnessInterface`
- `agda:postulate:chain-depth-bound`
- `agda:function:Self-_cell_obs-keys`
- `agda:module:Infinity`
- `agda:function:powerSetBound`
- `agda:function:Self-_merge_residue_sets`
- `agda:function:char2`
- `agda:function:Self-tau-_assign`
- `agda:module:TechniqueProfile`
- `agda:function:Self-nodes-append`
- `agda:function:𝟘`
- `agda:function:e₁-a₀`
- `agda:module:InternalHom`
- `agda:function:_∈S_`
- `agda:function:Self-find`
- `agda:function:η-ghost-cleavage-L0x3ax28x27allη-Constant-strx27x2c_x27allη-Constant-strx27x2c_x27allη-Constant-strx27x29`
- `agda:data:_∈ℕ_`
- `agda:record:IsPullback`
- `agda:function:Self-_eta_uf-union`
- `agda:record_field:retro-window`
- `agda:module:SelfEnrichment`
- `agda:module:Homotopy`
- `agda:function:residue-a₀-a₂`
- `agda:function:Self-_cascade_eta`

## Paper-only (no high-confidence Agda or Python match)

71 paper decls are not in the committed-triples set.  First 40:

- `paper:definition:def:residue`
- `paper:definition:def:nattrans`
- `paper:theorem:thm:adjunction`
- `paper:remark:rem:interchange-russell`
- `paper:definition:def:site`
- `paper:proposition:prop:limits`
- `paper:proposition:prop:k-morph`
- `paper:proposition:prop:dynamics-transfer`
- `paper:definition:def:composition`
- `paper:proposition:prop:monoidal`
- `paper:definition:def:operationalist`
- `paper:definition:def:coverage`
- `paper:remark:rem:2cat`
- `paper:remark:rem:cycles`
- `paper:theorem:thm:self-hosting`
- `paper:remark:rem:triangle-grounding`
- `paper:proposition:prop:monotone`
- `paper:definition:def:representable`
- `paper:definition:def:boundary`
- `paper:proposition:prop:2morph`
- `paper:definition:def:kappa`
- `paper:theorem:thm:cat-axioms`
- `paper:remark:rem:interchange-selfhosting`
- `paper:remark:rem:hott-paths`
- `paper:remark:rem:hyper-recursive`
- `paper:proposition:prop:commutative`
- `paper:definition:def:info-order`
- `paper:definition:def:powerset`
- `paper:corollary:cor:truncation-ambiguity`
- `paper:proposition:prop:bool-dependent`
- `paper:definition:def:eval`
- `paper:proposition:prop:growth`
- `paper:conjecture:conj:CH`
- `paper:definition:def:eval-linear`
- `paper:proposition:prop:naturality`
- `paper:definition:def:profile`
- `paper:corollary:cor:free-direction`
- `paper:theorem:prop:periodic-2d`
- `paper:example:ex:2morph`
- `paper:remark:rem:diaconescu`

## Python-only (no high-confidence Paper or Agda match)

115 Python decls are not in the committed-triples set.  First 40:

- `python:function:bytes_to_tree`
- `python:function:self_inverse_check`
- `python:function:_string_kind_tag`
- `python:function:module_to_tree`
- `python:function:is_residue`
- `python:function:make_string_registry`
- `python:function:ext_boundary`
- `python:function:byte_children`
- `python:function:compose_witnesses`
- `python:function:check_swap_involutive`
- `python:module:pyast`
- `python:module:walker`
- `python:class:DiscriminatorRegistry`
- `python:function:check_eval_linearity`
- `python:module:exterior`
- `python:function:_build_field`
- `python:function:dot`
- `python:function:interchange`
- `python:function:rotate`
- `python:function:tensor_witness`
- `python:module:pff_json`
- `python:function:check_bilinear_right`
- `python:function:_build_ast_node`
- `python:function:profile`
- `python:function:_mint_id`
- `python:function:parse_to_tree`
- `python:function:_char_seg`
- `python:function:check_profile_linearity`
- `python:module:adapter`
- `python:module:projections`
- `python:class:ToyBinaryClassifier`
- `python:function:check_profile_linearity_exhaustive`
- `python:function:make_list_registry`
- `python:function:check_double_cancel`
- `python:function:check_boundary_squared_all`
- `python:module:category`
- `python:module:cstz`
- `python:function:_build`
- `python:function:make_naming_registry`
- `python:module:toy`
