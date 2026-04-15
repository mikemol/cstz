# Gap analysis — what each side is missing

This report classifies every named object in paper / agda / python
into its **3×3 cofiber cell** (E=explicit in triple, M=missing).
The interesting cells are the non-EEE ones: they identify concrete
completeness obligations for the paper, for the formalisation, and
for the runtime.

## Summary

| Cell | Count | Meaning |
|------|-------|---------|
| E/E/E | 101 | Committed triple: paper+agda+python all present and aligned |
| E/M/M | 114 | Paper object without triple — need agda+python or clearer name |
| M/E/M | 339 | Agda decl without triple — either algebraic lemma (acceptable) or paper needs to state it |
| M/M/E | 142 | Python object without triple — ad-hoc runtime or classification/observe subsystem |

## Partial-signal gaps (high value actionable items)

The rows below are objects NOT in a committed triple that nevertheless
have a high-score 2-way match on one of the other corners — meaning
the third corner is the specific gap.

### Paper objects with strong Agda match but no Python (E/E/M candidates)

Paper concepts with a plausible Agda correlate but no Python runtime.
Action: implement these in `src/cstz/`, or document why they are purely
structural (no runtime witness needed).

| paper | best agda | score |
|-------|-----------|-------|
| definition:def:membership | module:CSTZ.Framework.Membership | 0.601 |
| definition:def:residue | function:isResidueχ | 0.588 |
| corollary:cor:free-direction | module:CSTZ.Higher | 0.578 |
| definition:def:internal-hom | function:internalHom | 0.571 |
| theorem:thm:adjunction | module:CSTZ.Category.Adjunction | 0.571 |
| proposition:prop:limits | module:CSTZ.Verification.LimitsExhaustive | 0.571 |
| definition:def:functor | record:DiscFunctor | 0.571 |
| definition:def:fibered | record:FiberedObj | 0.569 |
| definition:def:site | record:Site | 0.565 |
| definition:def:operationalist | module:CSTZ.Axiom.Operationalist | 0.565 |
| corollary:cor:self-model | function:wedge-self-zero | 0.564 |
| proposition:prop:perspectives | module:CSTZ.Higher.Perspectives | 0.562 |
| definition:def:swap-conj | module:CSTZ.Examples.GF2Cubed.Topos | 0.555 |
| proposition:prop:bool-dependent | function:isDiscriminated | 0.554 |
| proposition:prop:presheaf-sheaf | module:CSTZ.Topos.Sheaf | 0.552 |
| theorem:thm:yoneda | module:CSTZ.Category.Yoneda | 0.547 |
| definition:def:boundary | module:CSTZ.Exterior.Boundary | 0.546 |
| definition:def:profile | module:CSTZ.Framework.Membership | 0.546 |
| definition:def:eval | record:DirectedMorphism | 0.545 |
| proposition:prop:empty | module:CSTZ.Sets.EmptyPairing | 0.541 |
| definition:def:kappa | function:_⊆κ_ | 0.541 |
| remark:rem:cycles | module:CSTZ.Examples.GF2Cubed.Cycles | 0.541 |
| definition:def:info-order | function:order-indep | 0.539 |
| theorem:thm:fano | function:fano-line-1 | 0.538 |
| remark:rem:triangle-grounding | module:CSTZ.Higher.Triangle | 0.536 |
| theorem:thm:self-hosting | module:CSTZ.Topos.SelfHosting | 0.534 |
| definition:def:n-groupoid | module:CSTZ.Homotopy.Groupoid | 0.530 |
| definition:def:infinity | module:CSTZ.Sets.Infinity | 0.523 |
| corollary:cor:pro-topos | module:CSTZ.Examples.GF2Cubed.Topos | 0.522 |
| proposition:prop:monoidal | function:sym-monoidal | 0.522 |
| … (9 more) | | |

### Paper objects with strong Python match but no Agda (E/M/E candidates)

Paper concepts realised at runtime but not formally verified.  Action:
add an Agda module or postulate.

| paper | best python | score |
|-------|-------------|-------|
| definition:def:residue | function:is_residue | 0.665 |
| proposition:prop:commutative | function:check_wedge_comm | 0.657 |
| definition:def:composition | class:DirectedMorphism | 0.652 |
| definition:def:swap-conj | function:omega_neg | 0.642 |
| definition:def:boundary | function:ext_boundary | 0.622 |
| proposition:prop:limits | module:category | 0.620 |
| definition:def:operationalist | function:is_paired | 0.617 |
| theorem:thm:fano | function:check_fano_lines | 0.611 |
| definition:def:evolution | function:is_residue | 0.597 |
| theorem:thm:cat-axioms | module:category | 0.596 |
| proposition:prop:k-morph | module:homotopy | 0.594 |
| definition:def:eval | function:is_paired | 0.590 |
| definition:def:profile | module:exterior | 0.589 |
| remark:rem:proof-assistant | module:axioms | 0.589 |
| definition:def:representable | class:DirectedMorphism | 0.588 |
| proposition:prop:perspectives | class:Perspective | 0.584 |
| theorem:thm:n1cat | module:category | 0.583 |
| theorem:prop:periodic-2d | module:exterior | 0.582 |
| proposition:prop:bool-dependent | module:framework | 0.579 |
| definition:def:functor | function:ext_boundary | 0.576 |
| definition:def:kappa | function:is_paired | 0.576 |
| proposition:prop:naturality | module:category | 0.574 |
| definition:def:nattrans | class:DirectedMorphism | 0.573 |
| definition:def:n-groupoid | function:check_wedge_self_zero | 0.570 |
| remark:rem:interchange-selfhosting | module:category | 0.569 |
| remark:rem:residue-origins | function:is_residue | 0.568 |
| proposition:prop:dynamics-transfer | class:Perspective | 0.565 |
| definition:def:comprehension | function:check_wedge_self_zero | 0.559 |
| definition:def:membership | function:membership | 0.555 |
| theorem:thm:self-hosting | function:check_wedge_self_zero | 0.547 |
| … (24 more) | | |

### True paper gaps — agda+python present, no plausible paper match (M/E/E)

Formally specified AND runtime-verified concepts where the paper has
**no** scoring candidate above 0.25.  These are the strongest signals
of genuine paper completeness gaps — the paper truly doesn't name
what Agda and Python both implement.  Action: add a definition or
remark to the paper, or document why the construct is "internal"
to the framework.

*106 items in this bucket.*

| agda | python (score) | best paper (low score) |
|------|----------------|------------------------|
| function:classify | function:classify (1.03) | remark:anon_061 (0.22) |
| function:measure | function:choice_measure (0.97) | remark:anon_105 (0.25) |
| function:linkVector | function:link_vector (0.87) | definition:def:profile-l (0.23) |
| function:evolve | function:evolve (0.76) | remark:anon_004 (0.21) |
| function:equalizerWitness | function:equalizer_witness (0.76) | proposition:prop:2morph (0.22) |
| module:CSTZ.Verification.ChainBound | function:link_vector (0.74) | proposition:prop:boundar (0.25) |
| function:cd-mul | function:check_cd_commutativity (0.74) | definition:def:cayley-di (0.22) |
| function:χ | function:chi (0.72) | proposition:prop:extrema (0.24) |
| function:·V-zeroˡ | function:vec_zero (0.72) | corollary:cor:self-model (0.22) |
| function:·V-zeroʳ | function:vec_zero (0.72) | corollary:cor:self-model (0.22) |
| function:disj-gap-gap | function:omega_disj (0.71) | proposition:prop:extrema (0.23) |
| function:restrictToGrade | function:ext_restrict_grade (0.71) | definition:def:discrimin (0.24) |
| function:inAnnihilator | function:in_annihilator (0.71) | proposition:prop:commuta (0.23) |
| function:scalar | function:ext_scalar (0.70) | remark:anon_105 (0.22) |
| function:measure-zero | function:choice_measure (0.69) | remark:anon_105 (0.22) |
| function:_∧Ω_ | function:omega_conj (0.69) | definition:def:subobj-cl (0.25) |
| function:cd-step1-comm | function:check_cd_commutativity (0.69) | definition:def:cayley-di (0.22) |
| module:CSTZ.Verification.FixedPointStab | function:check_fixed_point_stability (0.67) | theorem:thm:entailed (0.24) |
| function:+F-cancel | function:check_double_cancel (0.67) | remark:rem:interchange-s (0.21) |
| function:+F-cancel⁻ | function:check_double_cancel (0.67) | remark:rem:interchange-s (0.21) |
| function:basis | function:ext_basis (0.67) | definition:def:boundary (0.22) |
| function:g0-grade | function:ext_grade (0.67) | remark:anon_099 (0.23) |
| function:neg-gap | function:omega_neg (0.66) | remark:anon_125 (0.24) |
| function:indist-diff | function:sym_diff_discriminator (0.66) | — |
| function:neg-overlap | function:omega_neg (0.66) | proposition:prop:extrema (0.24) |
| function:link-v₂ | function:link_vector (0.66) | remark:rem:cycles (0.21) |
| function:link-v₃ | function:link_vector (0.66) | remark:rem:cycles (0.21) |
| function:dne-gap | function:dne (0.66) | proposition:prop:extrema (0.23) |
| function:dne-overlap | function:dne (0.66) | proposition:prop:extrema (0.24) |
| function:compose-disjoint | function:compose_witnesses (0.66) | corollary:cor:self-model (0.03) |
| function:compose-witnesses | function:compose_witnesses (0.65) | proposition:prop:2morph (0.22) |
| function:dne-check | function:dne (0.65) | definition:def:subobj-cl (0.04) |
| function:+V-cancel | function:check_double_cancel (0.64) | remark:rem:interchange-s (0.21) |
| function:g3-top-grade | function:unique_top_form (0.64) | remark:anon_105 (0.23) |
| function:cycle2-link | function:link_vector (0.63) | remark:rem:cycles (0.21) |
| function:𝟘 | function:vec_zero (0.63) | corollary:cor:self-model (0.22) |
| function:pair-annihilator-e₁ | function:in_annihilator (0.63) | definition:def:membershi (0.24) |
| function:pair-annihilator-e₃ | function:in_annihilator (0.63) | definition:def:membershi (0.24) |
| function:classify-outside | function:classify (0.62) | remark:anon_061 (0.22) |
| function:annihilator-to-equality | function:in_annihilator (0.61) | definition:anon_013 (0.23) |
| … (66 more) | | |

### Near-triples — all three corners have signal but ambiguity blocked commit

These are items that would be committed triples if the alignment engine
had resolved the ambiguity correctly: agda has a strong python match
AND a plausible paper match (≥0.40).  If a human reviewer agrees with
the paper candidate, these are **alignment-engine failures to recover**,
not gaps.  They are the highest-leverage targets for refining the
alignment pipeline.

*111 items in this bucket.*

| agda | python | paper | py+paper score |
|------|--------|-------|----------------|
| function:isResidueχ | function:is_residue (0.89) | definition:def:residue (0.59) | 1.48 |
| function:fano-line-1 | function:verify_fano_line (0.85) | theorem:thm:fano (0.54) | 1.39 |
| function:fano-line-2 | function:verify_fano_line (0.85) | theorem:thm:fano (0.54) | 1.39 |
| function:fano-line-3 | function:verify_fano_line (0.85) | theorem:thm:fano (0.54) | 1.39 |
| function:fano-line-4 | function:verify_fano_line (0.85) | theorem:thm:fano (0.54) | 1.39 |
| function:fano-line-5 | function:verify_fano_line (0.85) | theorem:thm:fano (0.54) | 1.39 |
| function:fano-line-6 | function:verify_fano_line (0.85) | theorem:thm:fano (0.54) | 1.39 |
| function:fano-line-7 | function:verify_fano_line (0.85) | theorem:thm:fano (0.54) | 1.39 |
| function:dim-κ | function:dim_kappa (0.81) | definition:def:kappa (0.54) | 1.35 |
| function:self-inverse | function:check_vec_self_invers (0.82) | corollary:cor:self-model (0.52) | 1.34 |
| function:isResidue | function:is_residue (0.79) | definition:def:residue (0.55) | 1.34 |
| function:sym-monoidal | function:sym_diff_discriminato (0.66) | proposition:prop:sym-monoida (0.65) | 1.31 |
| function:self-inverse-morphism | function:check_vec_self_invers (0.77) | definition:def:directed-morp (0.53) | 1.30 |
| function:conj-τ-τ | function:omega_conj (0.76) | definition:def:swap-conj (0.54) | 1.30 |
| function:conj-σ-σ | function:omega_conj (0.76) | definition:def:swap-conj (0.54) | 1.30 |
| function:conj-over-τ | function:omega_conj (0.74) | definition:def:swap-conj (0.55) | 1.30 |
| function:conj-overlap-τ | function:omega_conj (0.74) | definition:def:swap-conj (0.54) | 1.27 |
| function:evolve-dim | function:evolve (0.74) | definition:def:boolean-dim (0.53) | 1.27 |
| module:CSTZ.Category.Directed | class:DirectedMorphism (0.68) | definition:def:directed-morp (0.59) | 1.27 |
| function:self-inverse-e₁e₂ | function:check_vec_self_invers (0.71) | corollary:cor:self-model (0.55) | 1.26 |
| function:conj-gap-any | function:omega_conj (0.73) | definition:def:swap-conj (0.52) | 1.26 |
| function:isDiscriminated | function:is_boolean (0.68) | proposition:prop:bool-depend (0.55) | 1.24 |
| function:+V-self | function:check_vec_self_invers (0.71) | corollary:cor:self-model (0.52) | 1.23 |
| function:∂∘∂≡0 | function:check_boundary_square (0.64) | proposition:prop:boundary (0.58) | 1.22 |
| function:_⊆κ_ | function:dim_kappa (0.67) | definition:def:kappa (0.54) | 1.21 |
| module:CSTZ.Framework.Membership | function:profile (0.61) | definition:def:membership (0.60) | 1.21 |
| function:∂ | function:check_boundary_square (0.60) | proposition:prop:boundary (0.60) | 1.20 |
| function:triangle-rot-σ | function:triangle_identity (0.66) | definition:def:tau-sigma (0.53) | 1.20 |
| module:CSTZ.Monoidal | module:monoidal (0.60) | theorem:thm:closure (0.60) | 1.20 |
| function:triangle-rot-τ | function:triangle_identity (0.66) | definition:def:tau-sigma (0.53) | 1.19 |
| function:monoidal-prod-coeff | function:compose_coeff (0.64) | definition:def:monoidal-prod (0.56) | 1.19 |
| module:CSTZ.Verification.ChoiceBound | function:choice_measure (0.67) | theorem:thm:choice (0.52) | 1.19 |
| module:CSTZ.Higher.Perspectives | function:rotate (0.63) | proposition:prop:perspective (0.56) | 1.19 |
| function:ext-a₀≢a₁ | function:ext_zero (0.67) | theorem:thm:ext (0.52) | 1.19 |
| function:ext-a₃≢a₅ | function:ext_zero (0.67) | theorem:thm:ext (0.52) | 1.19 |
| function:fano-1 | function:verify_fano_line (0.67) | theorem:thm:fano (0.52) | 1.19 |
| function:fano-4 | function:verify_fano_line (0.67) | theorem:thm:fano (0.52) | 1.19 |
| function:fano-7 | function:verify_fano_line (0.67) | theorem:thm:fano (0.52) | 1.19 |
| function:russell-at-zero | function:check_linear_map_zero (0.66) | theorem:thm:russell (0.52) | 1.18 |
| module:CSTZ.Topos.Fano | function:verify_fano_line (0.63) | theorem:thm:fano (0.53) | 1.17 |
| … (71 more) | | | |

## Single-source items (cofiber tips)

### Paper-only (E/M/M)

114 paper decls have no plausible agda or python match.
Most are likely **remarks** and **examples** that are rhetorical
context rather than formal objects to be mechanised.  First 20:

- `paper:definition:def:operationalist`  *definition*
- `paper:definition:def:profile`  *definition*
- `paper:definition:def:residue`  *definition*
- `paper:remark:rem:residue-origins`  *remark*
- `paper:definition:def:kappa`  *definition*
- `paper:definition:def:evolution`  *definition*
- `paper:proposition:prop:monotone`  *proposition*
- `paper:proposition:prop:monoidal`  *proposition*
- `paper:definition:def:membership`  *definition*
- `paper:definition:def:comprehension`  *definition*
- `paper:proposition:prop:nondefault`  *proposition*
- `paper:remark:rem:cycles`  *remark*
- `paper:proposition:prop:empty`  *proposition*
- `paper:definition:def:powerset`  *definition*
- `paper:conjecture:conj:CH`  *conjecture*
- `paper:definition:def:infinity`  *definition*
- `paper:remark:rem:foundational-status`  *remark*
- `paper:remark:rem:halting`  *remark*
- `paper:remark:rem:hyper-recursive`  *remark*
- `paper:remark:rem:proof-assistant`  *remark*

### Agda-only (M/E/M)

339 agda decls have no paper/python match.  Many are
low-level algebraic lemmas in GF2/Vec/Exterior — acceptable per
STUDY.md §8.  First 20:

- `agda:module:CSTZ.Axiom.Operationalist`  (*module*, /home/user/cstz/agda/CSTZ/Axiom/Operationalist.agda)
- `agda:module:CSTZ.Category.Adjunction`  (*module*, /home/user/cstz/agda/CSTZ/Category/Adjunction.agda)
- `agda:record:Adjunction`  (*record*, /home/user/cstz/agda/CSTZ/Category/Adjunction.agda)
- `agda:data:Axis`  (*data*, /home/user/cstz/agda/CSTZ/Category/Adjunction.agda)
- `agda:module:CSTZ.Category.Directed`  (*module*, /home/user/cstz/agda/CSTZ/Category/Directed.agda)
- `agda:module:CSTZ.Category.Emergent`  (*module*, /home/user/cstz/agda/CSTZ/Category/Emergent.agda)
- `agda:record:DiscCtx`  (*record*, /home/user/cstz/agda/CSTZ/Category/Emergent.agda)
- `agda:function:σ-target`  (*function*, /home/user/cstz/agda/CSTZ/Category/Emergent.agda)
- `agda:function:compose-witnesses`  (*function*, /home/user/cstz/agda/CSTZ/Category/Emergent.agda)
- `agda:module:CSTZ.Category.Functor`  (*module*, /home/user/cstz/agda/CSTZ/Category/Functor.agda)
- `agda:record:DiscFunctor`  (*record*, /home/user/cstz/agda/CSTZ/Category/Functor.agda)
- `agda:function:project`  (*function*, /home/user/cstz/agda/CSTZ/Category/Functor.agda)
- `agda:function:include`  (*function*, /home/user/cstz/agda/CSTZ/Category/Functor.agda)
- `agda:module:CSTZ.Category.Limits`  (*module*, /home/user/cstz/agda/CSTZ/Category/Limits.agda)
- `agda:function:equalizerWitness`  (*function*, /home/user/cstz/agda/CSTZ/Category/Limits.agda)
- `agda:module:CSTZ.Category.NatTrans`  (*module*, /home/user/cstz/agda/CSTZ/Category/NatTrans.agda)
- `agda:record:NatTrans`  (*record*, /home/user/cstz/agda/CSTZ/Category/NatTrans.agda)
- `agda:module:CSTZ.Category.TwoCategory`  (*module*, /home/user/cstz/agda/CSTZ/Category/TwoCategory.agda)
- `agda:function:interchange-at-F`  (*function*, /home/user/cstz/agda/CSTZ/Category/TwoCategory.agda)
- `agda:module:CSTZ.Category.Yoneda`  (*module*, /home/user/cstz/agda/CSTZ/Category/Yoneda.agda)

### Python-only (M/M/E)

142 python decls have no paper/agda match.  Most come
from the `classify/` and `observe.py` subsystems — Python-native
runtime concerns per STUDY.md §8.3.  First 20:

- `python:module:__init__`  (*module*, /home/user/cstz/src/cstz/__init__.py)
- `python:function:check_profile_linearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_eval_linearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_bilinearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_operationalist`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:module:category`  (*module*, /home/user/cstz/src/cstz/category.py)
- `python:function:compose_witnesses`  (*function*, /home/user/cstz/src/cstz/category.py)
- `python:function:interchange`  (*function*, /home/user/cstz/src/cstz/category.py)
- `python:function:equalizer_witness`  (*function*, /home/user/cstz/src/cstz/category.py)
- `python:module:__init__`  (*module*, /home/user/cstz/src/cstz/classify/__init__.py)
- `python:module:adapter`  (*module*, /home/user/cstz/src/cstz/classify/adapter.py)
- `python:function:emit_patch`  (*function*, /home/user/cstz/src/cstz/classify/adapter.py)
- `python:module:base`  (*module*, /home/user/cstz/src/cstz/classify/base.py)
- `python:class:ShapeWitness`  (*class*, /home/user/cstz/src/cstz/classify/base.py)
- `python:class:Classified`  (*class*, /home/user/cstz/src/cstz/classify/base.py)
- `python:class:Classifier`  (*class*, /home/user/cstz/src/cstz/classify/base.py)
- `python:module:bytes`  (*module*, /home/user/cstz/src/cstz/classify/bytes.py)
- `python:class:ByteNil`  (*class*, /home/user/cstz/src/cstz/classify/bytes.py)
- `python:class:ByteLeaf`  (*class*, /home/user/cstz/src/cstz/classify/bytes.py)
- `python:class:ByteSeg`  (*class*, /home/user/cstz/src/cstz/classify/bytes.py)
