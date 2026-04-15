# Gap analysis — what each side is missing

This report classifies every named object in paper / agda / python
into its **3×3 cofiber cell** (E=explicit in triple, M=missing).
The interesting cells are the non-EEE ones: they identify concrete
completeness obligations for the paper, for the formalisation, and
for the runtime.

## Summary

| Cell | Count | Meaning |
|------|-------|---------|
| E/E/E | 174 | Committed triple: paper+agda+python all present and aligned |
| E/M/M | 94 | Paper object without triple — need agda+python or clearer name |
| M/E/M | 266 | Agda decl without triple — either algebraic lemma (acceptable) or paper needs to state it |
| M/M/E | 119 | Python object without triple — ad-hoc runtime or classification/observe subsystem |

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
| theorem:thm:entailed | function:unique_top_form | 0.540 |
| theorem:thm:irremovable | function:exhaustive_filling | 0.539 |
| corollary:cor:pro-topos | module:topos | 0.538 |
| remark:rem:hyper-recursive | function:bytes_to_tree | 0.528 |
| theorem:thm:self-enrich | function:check_wedge_self_zero | 0.522 |
| conjecture:conj:CH | function:omega_conj | 0.519 |
| … (11 more) | | |

### True paper gaps — agda+python present, no plausible paper match (M/E/E)

Formally specified AND runtime-verified concepts where the paper has
**no** scoring candidate above 0.25.  These are the strongest signals
of genuine paper completeness gaps — the paper truly doesn't name
what Agda and Python both implement.  Action: add a definition or
remark to the paper, or document why the construct is "internal"
to the framework.

*94 items in this bucket.*

| agda | python (score) | best paper (low score) |
|------|----------------|------------------------|
| function:classify | function:classify (1.03) | remark:anon_061 (0.22) |
| function:cd-mul | function:check_cd_commutativity (0.74) | definition:def:cayley-di (0.22) |
| function:·V-zeroˡ | function:vec_zero (0.73) | corollary:cor:self-model (0.22) |
| function:·V-zeroʳ | function:vec_zero (0.73) | corollary:cor:self-model (0.22) |
| function:restrictToGrade | function:ext_restrict_grade (0.72) | definition:def:discrimin (0.24) |
| function:disj-gap-gap | function:omega_disj (0.72) | proposition:prop:extrema (0.23) |
| function:inAnnihilator | function:in_annihilator (0.71) | proposition:prop:commuta (0.23) |
| function:dne | function:dne (0.69) | definition:def:subobj-cl (0.05) |
| function:cd-step1-comm | function:check_cd_commutativity (0.69) | definition:def:cayley-di (0.22) |
| function:g0-grade | function:ext_grade (0.68) | remark:anon_099 (0.23) |
| function:+F-cancel | function:check_double_cancel (0.68) | remark:rem:interchange-s (0.21) |
| function:+F-cancel⁻ | function:check_double_cancel (0.68) | remark:rem:interchange-s (0.21) |
| function:dne-gap | function:dne (0.66) | proposition:prop:extrema (0.23) |
| function:univ-diff | function:sym_diff_discriminator (0.66) | — |
| function:indist-diff | function:sym_diff_discriminator (0.66) | — |
| function:compose-coeff | function:compose_coeff (0.66) | — |
| function:compose-disjoint | function:compose_witnesses (0.66) | corollary:cor:self-model (0.03) |
| function:dne-check | function:dne (0.65) | definition:def:subobj-cl (0.04) |
| function:g3-top-grade | function:unique_top_form (0.64) | remark:anon_105 (0.23) |
| function:𝟘 | function:vec_zero (0.63) | corollary:cor:self-model (0.22) |
| module:CSTZ.Verification.Annihilator | function:in_annihilator (0.63) | remark:anon_126 (0.01) |
| function:classify-outside | function:classify (0.62) | remark:anon_061 (0.22) |
| function:classify-inside | function:classify (0.62) | remark:anon_061 (0.22) |
| module:CSTZ.Vec | function:vec_zero (0.62) | — |
| module:CSTZ.Examples.TruthTables | function:check_truth_tables (0.62) | remark:rem:proof-assista (0.21) |
| function:+F-identity-𝟘ˡ | function:vec_zero (0.62) | definition:def:enrichmen (0.24) |
| module:CSTZ.GF2 | function:gf2_mul (0.61) | — |
| function:g0-basis | function:basis (0.61) | definition:def:boundary (0.22) |
| function:basisEq | function:basis (0.61) | definition:def:boundary (0.25) |
| module:CSTZ.Topos.FixedPoint | function:check_fixed_point_stability (0.61) | definition:anon_014 (0.23) |
| function:annihilator-to-equality | function:in_annihilator (0.61) | definition:anon_013 (0.23) |
| function:GF2Vec | function:vec_zero (0.60) | definition:def:represent (0.03) |
| module:CSTZ.Exterior.Wedge | function:check_wedge_comm (0.60) | proposition:prop:commuta (0.24) |
| function:grade | function:ext_grade (0.60) | remark:anon_099 (0.23) |
| module:CSTZ.Verification.FixedPointStab | function:check_fixed_point_stability (0.60) | definition:anon_014 (0.23) |
| function:+V-identityˡ | function:triangle_identity (0.59) | definition:def:enrichmen (0.23) |
| function:+V-identityʳ | function:triangle_identity (0.59) | definition:def:enrichmen (0.23) |
| function:Ω | function:omega_disj (0.59) | definition:def:subobj-cl (0.25) |
| module:CSTZ.Verification.CDHexagon | function:check_cd_commutativity (0.59) | remark:anon_126 (0.24) |
| function:_⊗-coeff_ | function:compose_coeff (0.59) | — |
| … (54 more) | | |

### Near-triples — all three corners have signal but ambiguity blocked commit

These are items that would be committed triples if the alignment engine
had resolved the ambiguity correctly: agda has a strong python match
AND a plausible paper match (≥0.40).  If a human reviewer agrees with
the paper candidate, these are **alignment-engine failures to recover**,
not gaps.  They are the highest-leverage targets for refining the
alignment pipeline.

*73 items in this bucket.*

| agda | python | paper | py+paper score |
|------|--------|-------|----------------|
| function:isResidueχ | function:is_residue (0.89) | definition:def:residue (0.59) | 1.48 |
| function:triangle-σ | function:triangle_identity (0.81) | definition:def:tau-sigma (0.54) | 1.35 |
| function:triangle-τ | function:triangle_identity (0.81) | definition:def:tau-sigma (0.54) | 1.34 |
| function:self-inverse | function:check_vec_self_invers (0.82) | corollary:cor:self-model (0.52) | 1.34 |
| function:conj-τ-σ | function:omega_conj (0.75) | definition:def:swap-conj (0.55) | 1.30 |
| function:conj-τ-σ | function:omega_conj (0.75) | definition:def:swap-conj (0.55) | 1.30 |
| function:conj-gap-any | function:omega_conj (0.74) | definition:def:swap-conj (0.52) | 1.26 |
| function:evolve-dim | function:evolve (0.73) | definition:def:boolean-dim (0.53) | 1.26 |
| function:self-inverse-e₁e₂ | function:check_vec_self_invers (0.71) | corollary:cor:self-model (0.55) | 1.26 |
| function:+V-self | function:check_vec_self_invers (0.72) | corollary:cor:self-model (0.52) | 1.24 |
| function:isDiscriminated | function:is_boolean (0.68) | proposition:prop:bool-depend (0.56) | 1.24 |
| function:∂∘∂≡0 | function:check_boundary_square (0.64) | proposition:prop:boundary (0.58) | 1.22 |
| function:_⊆κ_ | function:dim_kappa (0.67) | definition:def:kappa (0.54) | 1.21 |
| module:CSTZ.Axiom.ProfileLinearity | function:check_profile_lineari (0.65) | definition:def:profile-linea (0.56) | 1.21 |
| function:∂ | function:check_boundary_square (0.60) | proposition:prop:boundary (0.60) | 1.20 |
| function:triangle-rot-σ | function:triangle_identity (0.66) | definition:def:tau-sigma (0.54) | 1.20 |
| function:triangle-rot-τ | function:triangle_identity (0.66) | definition:def:tau-sigma (0.53) | 1.20 |
| module:CSTZ.Exterior.Boundary | function:check_boundary_square (0.60) | proposition:prop:boundary (0.60) | 1.19 |
| function:wedge-self-zero | function:check_wedge_self_zero (0.62) | corollary:cor:self-model (0.57) | 1.19 |
| function:fano-1 | function:verify_fano_line (0.67) | theorem:thm:fano (0.52) | 1.19 |
| function:fano-4 | function:verify_fano_line (0.67) | theorem:thm:fano (0.52) | 1.19 |
| function:fano-7 | function:verify_fano_line (0.67) | theorem:thm:fano (0.52) | 1.19 |
| function:ext-a₀≢a₁ | function:ext_zero (0.66) | theorem:thm:ext (0.52) | 1.18 |
| function:ext-a₃≢a₅ | function:ext_zero (0.66) | theorem:thm:ext (0.52) | 1.18 |
| function:russell-at-zero | function:check_linear_map_zero (0.66) | theorem:thm:russell (0.52) | 1.18 |
| function:russell-exclusion | function:russell_exclusion (0.63) | remark:rem:interchange-russe (0.54) | 1.16 |
| function:swap | function:check_swap_involutive (0.63) | definition:def:swap-conj (0.53) | 1.16 |
| function:profile-lin-check-1 | function:check_profile_lineari (0.63) | definition:def:profile-linea (0.52) | 1.15 |
| function:profile-lin-check-2 | function:check_profile_lineari (0.63) | definition:def:profile-linea (0.52) | 1.15 |
| module:CSTZ.Axiom.EvalLinearity | function:check_eval_linearity_ (0.63) | definition:def:eval (0.52) | 1.15 |
| module:CSTZ.Topos.SelfEnrichment | function:check_vec_self_invers (0.59) | definition:def:enrichment-da (0.56) | 1.14 |
| module:CSTZ.Verification.LimitsExhaustiv | function:check_profile_lineari (0.58) | proposition:prop:limits (0.55) | 1.13 |
| module:CSTZ.Higher.Triangle | function:triangle_identity (0.61) | definition:def:triangle (0.52) | 1.13 |
| function:gradeComponent | function:ext_grade (0.58) | definition:def:complex (0.54) | 1.12 |
| module:CSTZ.Topos.SelfHosting | function:check_vec_self_invers (0.59) | theorem:thm:self-hosting (0.53) | 1.12 |
| module:CSTZ.Verification.PairingBilinear | function:check_bilinear_left (0.60) | proposition:prop:pairing (0.52) | 1.12 |
| function:residue-a₀-a₂ | function:is_residue (0.58) | definition:def:residue (0.53) | 1.11 |
| function:toLinear | function:check_linear_map_zero (0.57) | definition:def:profile-linea (0.54) | 1.11 |
| module:CSTZ.Framework.Discriminator | function:sym_diff_discriminato (0.59) | definition:def:discriminator (0.52) | 1.11 |
| function:disjoint-self-false | function:check_vec_self_invers (0.56) | corollary:cor:self-model (0.55) | 1.11 |
| … (33 more) | | | |

## Single-source items (cofiber tips)

### Paper-only (E/M/M)

94 paper decls have no plausible agda or python match.
Most are likely **remarks** and **examples** that are rhetorical
context rather than formal objects to be mechanised.  First 20:

- `paper:definition:def:discriminator`  *definition*
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
- `paper:definition:def:complex`  *definition*

### Agda-only (M/E/M)

266 agda decls have no paper/python match.  Many are
low-level algebraic lemmas in GF2/Vec/Exterior — acceptable per
STUDY.md §8.  First 20:

- `agda:module:CSTZ.All`  (*module*, /home/user/cstz/agda/CSTZ/All.agda)
- `agda:module:CSTZ.Axiom.EvalLinearity`  (*module*, /home/user/cstz/agda/CSTZ/Axiom/EvalLinearity.agda)
- `agda:module:CSTZ.Axiom.ProfileLinearity`  (*module*, /home/user/cstz/agda/CSTZ/Axiom/ProfileLinearity.agda)
- `agda:function:compose-coeff`  (*function*, /home/user/cstz/agda/CSTZ/Category/Emergent.agda)
- `agda:function:project`  (*function*, /home/user/cstz/agda/CSTZ/Category/Functor.agda)
- `agda:function:include`  (*function*, /home/user/cstz/agda/CSTZ/Category/Functor.agda)
- `agda:record:NatTrans`  (*record*, /home/user/cstz/agda/CSTZ/Category/NatTrans.agda)
- `agda:function:yoneda-faithful`  (*function*, /home/user/cstz/agda/CSTZ/Category/Yoneda.agda)
- `agda:function:compose-e₁-e₂`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:compose-disjoint`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:retract-e₁`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:yoneda-A-B`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:yoneda-A-B'`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:yoneda-A-C`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:function:yoneda-A-D`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Category.agda)
- `agda:module:CSTZ.Examples.GF2Cubed.Cycles`  (*module*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Cycles.agda)
- `agda:function:cycle3-v₁`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Cycles.agda)
- `agda:function:cycle3-v₂`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Cycles.agda)
- `agda:function:cycle3-v₃`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Cycles.agda)
- `agda:function:cycle3-closes`  (*function*, /home/user/cstz/agda/CSTZ/Examples/GF2Cubed/Cycles.agda)

### Python-only (M/M/E)

119 python decls have no paper/agda match.  Most come
from the `classify/` and `observe.py` subsystems — Python-native
runtime concerns per STUDY.md §8.3.  First 20:

- `python:module:axioms`  (*module*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_profile_linearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_eval_linearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:check_bilinearity`  (*function*, /home/user/cstz/src/cstz/axioms.py)
- `python:function:compose_coeff`  (*function*, /home/user/cstz/src/cstz/category.py)
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
- `python:function:byte_children`  (*function*, /home/user/cstz/src/cstz/classify/bytes.py)
