# Gap analysis — what each side is missing

This report classifies every named object in paper / agda / python
into its **3×3 cofiber cell** (E=explicit in triple, M=missing).
The interesting cells are the non-EEE ones: they identify concrete
completeness obligations for the paper, for the formalisation, and
for the runtime.

## Summary

| Cell | Count | Meaning |
|------|-------|---------|
| E/E/E | 53 | Committed triple: paper+agda+python all present and aligned |
| E/M/M | 135 | Paper object without triple — need agda+python or clearer name |
| M/E/M | 387 | Agda decl without triple — either algebraic lemma (acceptable) or paper needs to state it |
| M/M/E | 156 | Python object without triple — ad-hoc runtime or classification/observe subsystem |

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
| proposition:prop:sym-monoidal | function:sym-monoidal | 0.670 |
| definition:def:subobj-class | module:CSTZ.Topos.SubobjClassifier | 0.646 |
| definition:def:residue | function:isResidueχ | 0.588 |
| definition:def:internal-hom | module:CSTZ.Monoidal.InternalHom | 0.574 |
| definition:def:functor | record:DiscFunctor | 0.573 |
| remark:rem:interchange-russell | function:claim-F | 0.572 |
| corollary:cor:self-model | function:wedge-self-zero | 0.570 |
| definition:def:fibered | record:FiberedObj | 0.569 |
| definition:def:membership | function:Membership | 0.568 |
| definition:def:site | record:Site | 0.566 |
| definition:def:monoidal-prod | function:monoidal-prod | 0.559 |
| theorem:thm:adjunction | record:Adjunction | 0.557 |
| proposition:prop:bool-dependent | function:isDiscriminated | 0.555 |
| definition:def:swap-conj | function:conj-over-τ | 0.555 |
| definition:def:tau-sigma | function:disj-τ-σ | 0.553 |
| proposition:prop:limits | module:CSTZ.Verification.LimitsExhaustive | 0.547 |
| definition:def:boundary | function:∂∘∂≡0 | 0.547 |
| corollary:cor:iterated-deloop | module:CSTZ.Monoidal.DeloopCollapse | 0.546 |
| definition:def:eval | record:DirectedMorphism | 0.546 |
| definition:def:directed-homotopy | record:DirectedMorphism | 0.545 |
| theorem:thm:closure | module:CSTZ.Monoidal.Closure | 0.543 |
| definition:def:complex | function:gradeComponent | 0.543 |
| definition:def:kappa | function:_⊆κ_ | 0.541 |
| theorem:thm:topos | module:CSTZ.Topos.FiberedTopos | 0.541 |
| corollary:cor:free-direction | module:CSTZ.Higher.FreeNK | 0.541 |
| theorem:thm:yoneda | function:yoneda-faithful | 0.541 |
| definition:def:info-order | function:order-indep | 0.540 |
| proposition:prop:univalence | function:univalence | 0.538 |
| proposition:prop:fol | module:CSTZ.Topos.FOL | 0.534 |
| theorem:thm:nk-free | module:CSTZ.Higher.FreeNK | 0.533 |
| … (27 more) | | |

### Paper objects with strong Python match but no Agda (E/M/E candidates)

Paper concepts realised at runtime but not formally verified.  Action:
add an Agda module or postulate.

| paper | best python | score |
|-------|-------------|-------|
| definition:def:residue | function:is_residue | 0.666 |
| proposition:prop:commutative | function:check_wedge_comm | 0.662 |
| definition:def:composition | class:DirectedMorphism | 0.653 |
| definition:def:swap-conj | function:omega_neg | 0.644 |
| proposition:prop:sym-monoidal | function:sym_diff_discriminator | 0.636 |
| definition:def:boundary | function:ext_boundary | 0.623 |
| proposition:prop:limits | module:category | 0.621 |
| remark:rem:interchange-russell | function:interchange | 0.600 |
| definition:def:evolution | function:is_residue | 0.597 |
| theorem:thm:cat-axioms | module:category | 0.596 |
| proposition:prop:k-morph | module:homotopy | 0.595 |
| definition:def:monoidal-prod | module:category | 0.591 |
| definition:def:eval | function:is_paired | 0.590 |
| definition:def:profile | module:exterior | 0.590 |
| definition:def:representable | class:DirectedMorphism | 0.590 |
| theorem:thm:closure | module:monoidal | 0.587 |
| definition:def:directed-homotopy | module:homotopy | 0.586 |
| theorem:prop:periodic-2d | module:exterior | 0.583 |
| definition:def:limit | module:category | 0.582 |
| theorem:thm:deloop | module:category | 0.582 |
| theorem:thm:n1cat | module:category | 0.582 |
| definition:def:complex | module:exterior | 0.580 |
| proposition:prop:bool-dependent | module:framework | 0.579 |
| definition:def:functor | function:ext_boundary | 0.578 |
| definition:def:kappa | function:is_paired | 0.576 |
| definition:def:nattrans | class:DirectedMorphism | 0.573 |
| proposition:prop:naturality | module:category | 0.573 |
| definition:def:discriminator | class:Discriminator | 0.573 |
| definition:def:n-groupoid | function:check_wedge_self_zero | 0.571 |
| definition:def:tau-sigma | class:DiscriminatorRegistry | 0.570 |
| … (41 more) | | |

### True paper gaps — agda+python present, no plausible paper match (M/E/E)

Formally specified AND runtime-verified concepts where the paper has
**no** scoring candidate above 0.25.  These are the strongest signals
of genuine paper completeness gaps — the paper truly doesn't name
what Agda and Python both implement.  Action: add a definition or
remark to the paper, or document why the construct is "internal"
to the framework.

*120 items in this bucket.*

| agda | python (score) | best paper (low score) |
|------|----------------|------------------------|
| function:classify | function:classify (1.03) | remark:anon_061 (0.22) |
| function:measure | function:choice_measure (0.98) | remark:anon_105 (0.25) |
| function:linkVector | function:link_vector (0.87) | definition:def:profile-l (0.23) |
| function:evolve | function:evolve (0.76) | remark:anon_004 (0.21) |
| function:equalizerWitness | function:equalizer_witness (0.76) | proposition:prop:2morph (0.22) |
| function:cd-mul | function:check_cd_commutativity (0.74) | definition:def:cayley-di (0.22) |
| function:·V-zeroˡ | function:vec_zero (0.73) | corollary:cor:self-model (0.22) |
| function:·V-zeroʳ | function:vec_zero (0.73) | corollary:cor:self-model (0.22) |
| function:χ | function:chi (0.72) | proposition:prop:extrema (0.24) |
| function:disj-gap-gap | function:omega_disj (0.72) | proposition:prop:extrema (0.23) |
| function:scalar | function:ext_scalar (0.71) | remark:anon_105 (0.22) |
| function:inAnnihilator | function:in_annihilator (0.71) | proposition:prop:commuta (0.23) |
| module:CSTZ.Exterior.Basis | function:ext_basis (0.70) | definition:def:boundary (0.22) |
| function:_∧Ω_ | function:omega_conj (0.69) | definition:def:subobj-cl (0.25) |
| function:basis | function:ext_basis (0.69) | definition:def:boundary (0.22) |
| function:measure-zero | function:choice_measure (0.69) | corollary:cor:self-model (0.22) |
| function:dne | function:dne (0.69) | definition:def:subobj-cl (0.05) |
| function:cd-step1-comm | function:check_cd_commutativity (0.69) | definition:def:cayley-di (0.22) |
| function:g0-grade | function:ext_grade (0.68) | remark:anon_099 (0.23) |
| function:+F-cancel | function:check_double_cancel (0.68) | remark:rem:interchange-s (0.21) |
| function:+F-cancel⁻ | function:check_double_cancel (0.68) | remark:rem:interchange-s (0.21) |
| function:neg-gap | function:omega_neg (0.66) | remark:anon_125 (0.24) |
| function:link-v₁ | function:link_vector (0.66) | remark:rem:cycles (0.21) |
| function:link-v₂ | function:link_vector (0.66) | remark:rem:cycles (0.21) |
| function:link-v₃ | function:link_vector (0.66) | remark:rem:cycles (0.21) |
| function:dne-gap | function:dne (0.66) | proposition:prop:extrema (0.23) |
| function:neg-overlap | function:omega_neg (0.66) | proposition:prop:extrema (0.24) |
| function:univ-diff | function:sym_diff_discriminator (0.66) | — |
| function:indist-diff | function:sym_diff_discriminator (0.66) | — |
| function:dne-overlap | function:dne (0.66) | proposition:prop:extrema (0.24) |
| function:compose-disjoint | function:compose_witnesses (0.66) | corollary:cor:self-model (0.03) |
| function:dne-check | function:dne (0.65) | definition:def:subobj-cl (0.04) |
| function:compose-witnesses | function:compose_witnesses (0.65) | proposition:prop:2morph (0.22) |
| function:+V-cancel | function:check_double_cancel (0.65) | remark:rem:interchange-s (0.21) |
| function:g3-top-grade | function:unique_top_form (0.64) | remark:anon_105 (0.23) |
| function:cycle2-link | function:link_vector (0.63) | remark:rem:cycles (0.21) |
| function:𝟘 | function:vec_zero (0.63) | corollary:cor:self-model (0.22) |
| module:CSTZ.Verification.Annihilator | function:in_annihilator (0.63) | remark:anon_126 (0.01) |
| function:pair-annihilator-e₁ | function:in_annihilator (0.63) | definition:def:membershi (0.24) |
| function:pair-annihilator-e₃ | function:in_annihilator (0.63) | definition:def:membershi (0.24) |
| … (80 more) | | |

### Near-triples — all three corners have signal but ambiguity blocked commit

These are items that would be committed triples if the alignment engine
had resolved the ambiguity correctly: agda has a strong python match
AND a plausible paper match (≥0.40).  If a human reviewer agrees with
the paper candidate, these are **alignment-engine failures to recover**,
not gaps.  They are the highest-leverage targets for refining the
alignment pipeline.

*135 items in this bucket.*

| agda | python | paper | py+paper score |
|------|--------|-------|----------------|
| data:LimitKind | class:LimitKind (1.00) | definition:def:limit (0.52) | 1.52 |
| function:isResidueχ | function:is_residue (0.89) | definition:def:residue (0.59) | 1.48 |
| function:dim-κ | function:dim_kappa (0.82) | definition:def:kappa (0.54) | 1.36 |
| function:isBoolean | function:is_boolean (0.81) | proposition:prop:bool-depend (0.55) | 1.36 |
| function:sym-monoidal | function:sym_diff_discriminato (0.68) | proposition:prop:sym-monoida (0.67) | 1.35 |
| function:self-inverse | function:check_vec_self_invers (0.82) | corollary:cor:self-model (0.52) | 1.34 |
| function:isResidue | function:is_residue (0.79) | definition:def:residue (0.55) | 1.34 |
| function:self-inverse-morphism | function:check_vec_self_invers (0.78) | definition:def:directed-morp (0.53) | 1.31 |
| function:conj-τ-τ | function:omega_conj (0.76) | definition:def:swap-conj (0.54) | 1.30 |
| function:conj-σ-σ | function:omega_conj (0.76) | definition:def:swap-conj (0.54) | 1.30 |
| function:conj-τ-σ | function:omega_conj (0.75) | definition:def:swap-conj (0.55) | 1.30 |
| function:conj-τ-σ | function:omega_conj (0.75) | definition:def:swap-conj (0.55) | 1.30 |
| function:conj-over-τ | function:omega_conj (0.75) | definition:def:swap-conj (0.55) | 1.30 |
| function:conj-overlap-τ | function:omega_conj (0.74) | definition:def:swap-conj (0.54) | 1.28 |
| function:neg-σ | function:omega_neg (0.73) | definition:def:tau-sigma (0.54) | 1.26 |
| function:conj-gap-any | function:omega_conj (0.74) | definition:def:swap-conj (0.52) | 1.26 |
| function:neg-τ | function:omega_neg (0.73) | definition:def:tau-sigma (0.54) | 1.26 |
| function:evolve-dim | function:evolve (0.73) | definition:def:boolean-dim (0.53) | 1.26 |
| function:self-inverse-e₁e₂ | function:check_vec_self_invers (0.71) | corollary:cor:self-model (0.55) | 1.26 |
| function:disj-τ-σ | function:omega_disj (0.69) | definition:def:tau-sigma (0.55) | 1.25 |
| function:+V-self | function:check_vec_self_invers (0.72) | corollary:cor:self-model (0.52) | 1.24 |
| function:isDiscriminated | function:is_boolean (0.68) | proposition:prop:bool-depend (0.56) | 1.24 |
| function:disj-gap-τ | function:omega_disj (0.69) | definition:def:tau-sigma (0.53) | 1.22 |
| function:∂∘∂≡0 | function:check_boundary_square (0.64) | proposition:prop:boundary (0.58) | 1.22 |
| function:_⊆κ_ | function:dim_kappa (0.67) | definition:def:kappa (0.54) | 1.21 |
| function:∂ | function:check_boundary_square (0.60) | proposition:prop:boundary (0.60) | 1.20 |
| function:monoidal-prod-coeff | function:compose_coeff (0.64) | definition:def:monoidal-prod (0.56) | 1.20 |
| function:triangle-rot-σ | function:triangle_identity (0.66) | definition:def:tau-sigma (0.54) | 1.20 |
| function:triangle-rot-τ | function:triangle_identity (0.66) | definition:def:tau-sigma (0.53) | 1.20 |
| module:CSTZ.Exterior.Boundary | function:check_boundary_square (0.60) | proposition:prop:boundary (0.60) | 1.19 |
| function:dne-σ | function:dne (0.66) | definition:def:tau-sigma (0.54) | 1.19 |
| function:dne-τ | function:dne (0.66) | definition:def:tau-sigma (0.54) | 1.19 |
| module:CSTZ.Topos.SubobjClassifier | class:ToyBinaryClassifier (0.55) | definition:def:subobj-class (0.65) | 1.19 |
| function:pairing-diff | function:sym_diff_discriminato (0.67) | proposition:prop:pairing (0.52) | 1.19 |
| function:fano-4 | function:verify_fano_line (0.67) | theorem:thm:fano (0.52) | 1.19 |
| function:fano-7 | function:verify_fano_line (0.67) | theorem:thm:fano (0.52) | 1.19 |
| function:ext-a₀≢a₁ | function:ext_zero (0.66) | theorem:thm:ext (0.52) | 1.18 |
| function:ext-a₃≢a₅ | function:ext_zero (0.66) | theorem:thm:ext (0.52) | 1.18 |
| function:russell-at-zero | function:check_linear_map_zero (0.66) | theorem:thm:russell (0.52) | 1.18 |
| function:triangle-check | function:ext_is_zero (0.65) | definition:def:triangle (0.52) | 1.17 |
| … (95 more) | | | |

## Single-source items (cofiber tips)

### Paper-only (E/M/M)

135 paper decls have no plausible agda or python match.
Most are likely **remarks** and **examples** that are rhetorical
context rather than formal objects to be mechanised.  First 20:

- `paper:definition:def:discriminator`  *definition*
- `paper:definition:def:tau-sigma`  *definition*
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
- `paper:theorem:thm:foundation`  *theorem*
- `paper:remark:rem:cycles`  *remark*
- `paper:proposition:prop:empty`  *proposition*
- `paper:proposition:prop:pairing`  *proposition*
- `paper:definition:def:powerset`  *definition*
- `paper:conjecture:conj:CH`  *conjecture*
- `paper:definition:def:infinity`  *definition*
- `paper:proposition:prop:infinity`  *proposition*

### Agda-only (M/E/M)

387 agda decls have no paper/python match.  Many are
low-level algebraic lemmas in GF2/Vec/Exterior — acceptable per
STUDY.md §8.  First 20:

- `agda:module:CSTZ.All`  (*module*, /home/user/cstz/agda/CSTZ/All.agda)
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
- `agda:data:LimitKind`  (*data*, /home/user/cstz/agda/CSTZ/Category/Limits.agda)
- `agda:function:equalizerWitness`  (*function*, /home/user/cstz/agda/CSTZ/Category/Limits.agda)
- `agda:module:CSTZ.Category.NatTrans`  (*module*, /home/user/cstz/agda/CSTZ/Category/NatTrans.agda)
- `agda:record:NatTrans`  (*record*, /home/user/cstz/agda/CSTZ/Category/NatTrans.agda)
- `agda:module:CSTZ.Category.TwoCategory`  (*module*, /home/user/cstz/agda/CSTZ/Category/TwoCategory.agda)
- `agda:function:interchange-at-F`  (*function*, /home/user/cstz/agda/CSTZ/Category/TwoCategory.agda)

### Python-only (M/M/E)

156 python decls have no paper/agda match.  Most come
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
- `python:class:LimitKind`  (*class*, /home/user/cstz/src/cstz/category.py)
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
