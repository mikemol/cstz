# Gap analysis — what each side is missing

This report classifies every named object in paper / agda / python
into its **3×3 cofiber cell** (E=explicit in triple, M=missing).
The interesting cells are the non-EEE ones: they identify concrete
completeness obligations for the paper, for the formalisation, and
for the runtime.

## Summary

| Cell | Count | Meaning |
|------|-------|---------|
| E/E/E | 154 | Committed triple: paper+agda+python all present and aligned |
| E/M/M | 98 | Paper object without triple — need agda+python or clearer name |
| M/E/M | 286 | Agda decl without triple — either algebraic lemma (acceptable) or paper needs to state it |
| M/M/E | 123 | Python object without triple — ad-hoc runtime or classification/observe subsystem |

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
| definition:def:enrichment-data | record:EnrichmentData | 0.655 |
| definition:def:residue | function:isResidueχ | 0.588 |
| corollary:cor:self-model | function:wedge-self-zero | 0.570 |
| definition:def:swap-conj | function:conj-over-τ | 0.555 |
| theorem:thm:self-enrich | module:CSTZ.Topos.SelfEnrichment | 0.545 |
| definition:def:complex | function:gradeComponent | 0.543 |
| theorem:thm:subobj | module:CSTZ.Topos.SubobjClassifier | 0.541 |
| corollary:cor:free-direction | module:CSTZ.Higher.FreeNK | 0.541 |
| proposition:prop:symdiff | function:symdiff-a₂ | 0.538 |
| proposition:prop:fol | module:CSTZ.Topos.FOL | 0.534 |
| definition:def:infinity | module:CSTZ.Sets.Infinity | 0.533 |
| corollary:cor:pro-topos | module:CSTZ.Topos | 0.532 |
| theorem:thm:sheaf | module:CSTZ.Topos.Sheaf | 0.532 |
| theorem:thm:deloop | module:CSTZ.Monoidal.DeloopCollapse | 0.530 |
| proposition:prop:infinity | module:CSTZ.Sets.Infinity | 0.528 |
| definition:def:triangle | function:triangle-σ | 0.528 |
| proposition:prop:empty | module:CSTZ.Sets.EmptyPairing | 0.525 |
| proposition:prop:presheaf-sheaf | module:CSTZ.Topos.Sheaf | 0.525 |
| definition:def:n-groupoid | module:CSTZ.Homotopy.Groupoid | 0.524 |
| proposition:prop:monoidal | module:CSTZ.Monoidal | 0.522 |
| conjecture:conj:CH | function:conj-over-τ | 0.522 |
| theorem:thm:ext | function:ext-a₀≢a₁ | 0.521 |
| theorem:thm:groupoid | module:CSTZ.Homotopy.Groupoid | 0.521 |
| remark:rem:residue-origins | function:isResidue | 0.521 |
| theorem:thm:irremovable | module:CSTZ.Topos.Irremovable | 0.520 |
| definition:def:discriminator | module:CSTZ.Framework.Discriminator | 0.518 |
| theorem:thm:exhaustive | module:CSTZ.Verification.LimitsExhaustive | 0.518 |
| remark:rem:native-univalence | module:CSTZ.Homotopy.Univalence | 0.513 |
| remark:rem:proof-assistant | module:CSTZ.Topos.ProofTheory | 0.505 |

### Paper objects with strong Python match but no Agda (E/M/E candidates)

Paper concepts realised at runtime but not formally verified.  Action:
add an Agda module or postulate.

| paper | best python | score |
|-------|-------------|-------|
| definition:def:residue | function:is_residue | 0.666 |
| proposition:prop:commutative | function:check_wedge_comm | 0.662 |
| definition:def:composition | class:DirectedMorphism | 0.653 |
| definition:def:swap-conj | function:omega_neg | 0.644 |
| definition:def:evolution | function:is_residue | 0.597 |
| theorem:thm:cat-axioms | module:category | 0.596 |
| proposition:prop:k-morph | module:homotopy | 0.595 |
| definition:def:representable | class:DirectedMorphism | 0.590 |
| remark:rem:proof-assistant | module:axioms | 0.589 |
| theorem:prop:periodic-2d | module:exterior | 0.583 |
| theorem:thm:deloop | module:category | 0.582 |
| theorem:thm:n1cat | module:category | 0.582 |
| definition:def:complex | module:exterior | 0.580 |
| definition:def:triangle | function:triangle_identity | 0.576 |
| theorem:thm:exhaustive | function:exhaustive_filling | 0.575 |
| definition:def:nattrans | class:DirectedMorphism | 0.573 |
| definition:def:discriminator | class:Discriminator | 0.573 |
| definition:def:n-groupoid | function:check_wedge_self_zero | 0.571 |
| remark:rem:residue-origins | function:is_residue | 0.569 |
| proposition:prop:dynamics-transfer | class:Perspective | 0.566 |
| theorem:thm:subobj | function:unique_top_form | 0.565 |
| definition:def:comprehension | function:check_wedge_self_zero | 0.560 |
| definition:def:enrichment-data | function:triangle_identity | 0.556 |
| theorem:thm:ext | function:ext_wedge | 0.548 |
| proposition:prop:monoidal | module:monoidal | 0.545 |
| corollary:cor:self-model | function:check_wedge_self_zero | 0.545 |
| proposition:prop:2morph | function:equalizer_witness | 0.544 |
| theorem:thm:entailed | function:unique_top_form | 0.540 |
| theorem:thm:irremovable | function:exhaustive_filling | 0.539 |
| corollary:cor:pro-topos | module:topos | 0.538 |
| … (15 more) | | |

### Agda-Python pairs where the paper is missing (M/E/E candidates)

Formally specified AND runtime-verified concepts that the paper does not
explicitly name.  These are the strongest signal of paper completeness
gaps.  Action: add a definition or remark to the paper, or document why
the construct is "internal" to the framework.

| agda | best python | score |
|------|-------------|-------|
| function:classify | function:classify | 1.035 |
| function:isResidueχ | function:is_residue | 0.893 |
| function:linkVector | function:link_vector | 0.872 |
| function:unique-top-form-grade | function:unique_top_form | 0.821 |
| function:self-inverse | function:check_vec_self_inverse | 0.820 |
| function:triangle-σ | function:triangle_identity | 0.812 |
| function:triangle-τ | function:triangle_identity | 0.809 |
| function:chain-link | function:link_vector | 0.802 |
| function:equalizerWitness | function:equalizer_witness | 0.755 |
| function:conj-τ-σ | function:omega_conj | 0.747 |
| function:conj-τ-σ | function:omega_conj | 0.747 |
| function:cd-mul | function:check_cd_commutativity | 0.741 |
| function:conj-gap-any | function:omega_conj | 0.738 |
| function:·V-zeroˡ | function:vec_zero | 0.734 |
| function:·V-zeroʳ | function:vec_zero | 0.734 |
| function:evolve-dim | function:evolve | 0.734 |
| function:restrictToGrade | function:ext_restrict_grade | 0.723 |
| function:χ | function:chi | 0.721 |
| function:+V-self | function:check_vec_self_inverse | 0.720 |
| function:disj-gap-gap | function:omega_disj | 0.717 |
| function:inAnnihilator | function:in_annihilator | 0.707 |
| function:self-inverse-e₁e₂ | function:check_vec_self_inverse | 0.705 |
| function:dne | function:dne | 0.688 |
| function:cd-step1-comm | function:check_cd_commutativity | 0.686 |
| function:isDiscriminated | function:is_boolean | 0.684 |
| function:g0-grade | function:ext_grade | 0.684 |
| function:+F-cancel | function:check_double_cancel | 0.678 |
| function:+F-cancel⁻ | function:check_double_cancel | 0.678 |
| function:_⊆κ_ | function:dim_kappa | 0.673 |
| function:fano-1 | function:verify_fano_line | 0.669 |
| function:fano-4 | function:verify_fano_line | 0.669 |
| function:fano-7 | function:verify_fano_line | 0.669 |
| function:ext-a₀≢a₁ | function:ext_zero | 0.663 |
| function:ext-a₃≢a₅ | function:ext_zero | 0.663 |
| function:triangle-rot-σ | function:triangle_identity | 0.663 |
| function:dne-gap | function:dne | 0.663 |
| function:univ-diff | function:sym_diff_discriminator | 0.662 |
| function:indist-diff | function:sym_diff_discriminator | 0.662 |
| function:russell-at-zero | function:check_linear_map_zero | 0.661 |
| function:triangle-rot-τ | function:triangle_identity | 0.661 |
| … (158 more) | | |

## Single-source items (cofiber tips)

### Paper-only (E/M/M)

98 paper decls have no plausible agda or python match.
Most are likely **remarks** and **examples** that are rhetorical
context rather than formal objects to be mechanised.  First 20:

- `paper:definition:def:discriminator`  *definition*
- `paper:definition:def:residue`  *definition*
- `paper:remark:rem:residue-origins`  *remark*
- `paper:definition:def:evolution`  *definition*
- `paper:proposition:prop:monotone`  *proposition*
- `paper:proposition:prop:monoidal`  *proposition*
- `paper:theorem:thm:ext`  *theorem*
- `paper:definition:def:comprehension`  *definition*
- `paper:proposition:prop:nondefault`  *proposition*
- `paper:proposition:prop:empty`  *proposition*
- `paper:proposition:prop:symdiff`  *proposition*
- `paper:conjecture:conj:CH`  *conjecture*
- `paper:definition:def:infinity`  *definition*
- `paper:proposition:prop:infinity`  *proposition*
- `paper:remark:rem:foundational-status`  *remark*
- `paper:remark:rem:halting`  *remark*
- `paper:remark:rem:hyper-recursive`  *remark*
- `paper:remark:rem:proof-assistant`  *remark*
- `paper:remark:rem:cwa-owa`  *remark*
- `paper:remark:rem:diaconescu`  *remark*

### Agda-only (M/E/M)

286 agda decls have no paper/python match.  Many are
low-level algebraic lemmas in GF2/Vec/Exterior — acceptable per
STUDY.md §8.  First 20:

- `agda:module:CSTZ.All`  (*module*, /home/user/cstz/agda/CSTZ/All.agda)
- `agda:module:CSTZ.Axiom.EvalLinearity`  (*module*, /home/user/cstz/agda/CSTZ/Axiom/EvalLinearity.agda)
- `agda:module:CSTZ.Axiom.ProfileLinearity`  (*module*, /home/user/cstz/agda/CSTZ/Axiom/ProfileLinearity.agda)
- `agda:function:compose-coeff`  (*function*, /home/user/cstz/agda/CSTZ/Category/Emergent.agda)
- `agda:function:project`  (*function*, /home/user/cstz/agda/CSTZ/Category/Functor.agda)
- `agda:function:include`  (*function*, /home/user/cstz/agda/CSTZ/Category/Functor.agda)
- `agda:function:equalizerWitness`  (*function*, /home/user/cstz/agda/CSTZ/Category/Limits.agda)
- `agda:module:CSTZ.Category.NatTrans`  (*module*, /home/user/cstz/agda/CSTZ/Category/NatTrans.agda)
- `agda:record:NatTrans`  (*record*, /home/user/cstz/agda/CSTZ/Category/NatTrans.agda)
- `agda:module:CSTZ.Category.TwoCategory`  (*module*, /home/user/cstz/agda/CSTZ/Category/TwoCategory.agda)
- `agda:function:yoneda-faithful`  (*function*, /home/user/cstz/agda/CSTZ/Category/Yoneda.agda)
- `agda:module:CSTZ.Category`  (*module*, /home/user/cstz/agda/CSTZ/Category.agda)
- `agda:module:CSTZ.Examples.GF2Cubed.Category`  (*module*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:compose-e₁-e₂`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:compose-disjoint`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:retract-e₁`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:yoneda-A-B`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:yoneda-A-B'`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:yoneda-A-C`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:yoneda-A-D`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)

### Python-only (M/M/E)

123 python decls have no paper/agda match.  Most come
from the `classify/` and `observe.py` subsystems — Python-native
runtime concerns per STUDY.md §8.3.  First 20:

- `python:module:axioms`  (*module*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_profile_linearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_eval_linearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_bilinearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:compose_coeff`  (*function*, /home/user/cstz/src/cstz/category.py)
- `python:function:equalizer_witness`  (*function*, /home/user/cstz/src/cstz/category.py)
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
- `python:function:morton2`  (*function*, /home/user/cstz/src/cstz/classify/bytes.py)
- `python:function:byte_key`  (*function*, /home/user/cstz/src/cstz/classify/bytes.py)
- `python:function:bytes_to_tree`  (*function*, /home/user/cstz/src/cstz/classify/bytes.py)
- `python:function:_build`  (*function*, /home/user/cstz/src/cstz/classify/bytes.py)
