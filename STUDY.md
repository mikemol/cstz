# STUDY — Cross-reference for `agda/` and `src/cstz/`

A side-by-side reading guide for the two codebases that implement
"Topos-Theoretic Grammar Induction and Adversarial PRNG via GF(2)
Sheafification" (see `Topos-Theoretic Grammar Induction and PRNG.md`).
The Agda formalization in `agda/CSTZ/` is the specification; the Python
package in `src/cstz/` is the runtime and projects observations into the
PFF JSON interchange format. This document (1) lists every phase of the
formalization alongside its Python mirror, (2) catalogs the 9 Agda
postulates with runtime counterparts where they exist, (3) slots the
Python-only subsystems (`observe`, `classify/`, `projections/`, `legacy/`)
against the mirror, and (4) proposes a reading order.

## 1. Repository layout

```
agda/
  cstz.agda-lib                    library, depends on standard-library-2.1
  CSTZ/
    All.agda                       imports every phase in order
    GF2.agda, Vec.agda             Phase 1: GF(2) scalars + vectors
    Exterior.agda + Exterior/      Phase 1: exterior algebra Λ(GF(2)^n)
    Axiom/                         Phase 2: three postulated axioms
    Framework.agda + Framework/    Phase 3: discrimination framework
    Sets.agda + Sets/              Phase 4: set-theoretic consequences
    Homotopy.agda + Homotopy/      Phase 5: chain complexes, exhaustivity
    Category.agda + Category/      Phase 6: functors, limits, Yoneda
    Higher.agda + Higher/          Phase 7: higher categories
    Monoidal.agda + Monoidal/      Phase 8: tensor, Cayley-Dickson
    Topos.agda + Topos/            Phase 9: subobject classifier, sheaves
    Examples.agda + Examples/      Phase 10: GF(2)^3 worked examples
    Meta/TechniqueProfile.agda     Phase 11: proof-technique metadata
    Verification/                  Appendix B gap-closers
src/cstz/
  __init__.py                      docstring-only public surface
  gf2.py, exterior.py              Phase 1 mirror
  axioms.py                        runtime validators for Phase 2 postulates
  framework.py                     Phase 3 mirror
  sets.py, homotopy.py             Phases 4–5 mirror
  category.py, higher.py,
    monoidal.py, topos.py          Phases 6–9 mirror
  examples.py                      Phase 10 mirror
  verification.py                  Appendix B mirror (exhaustive checks at small n)
  observe.py                       Python-only: witness logging
  classify/                        Python-only: τ-identity classifier engine
  projections/pff_json.py          Python-only: serializer to pff.schema.json
  legacy/                          superseded SPPF/PFF stack (coverage-excluded)
CoreProof.agda                     root: generated 7,500-node AST proof witness
inference.agda                     root: standalone SPPF reference spec
rhpf-pff-profiles/pff.schema.json  serialization target
tests/test_*.py                    per-phase pytest; fail_under = 100 in pyproject.toml
```

## 2. Phase-by-phase correspondence

Each row aligns one Agda phase with its Python mirror. Postulate IDs
(P1..P9) expand in §3. "Tests" names the pytest file(s) that exercise the
row.

| # | Phase | Agda | Python | Key exports | Postulates | Tests |
|---|-------|------|--------|-------------|------------|-------|
| 1 | GF(2) + Vec | `CSTZ.GF2` (+ `GF2/Properties`), `CSTZ.Vec` (+ `Vec/Properties`) | `cstz.gf2` | `gf2_add`, `gf2_mul`, `dot`, `basis`, `vec_add`, `popcount` | — | `test_gf2.py` |
| 1′ | Exterior algebra | `CSTZ.Exterior` + `Exterior/{Basis,Wedge,Boundary,Graded}` | `cstz.exterior` | `ext_wedge`, `ext_boundary`, `ext_grade`, `ext_basis`, `ext_is_zero` | **P4** | `test_exterior.py` |
| 2 | Axioms | `CSTZ.Axiom.{ProfileLinearity,EvalLinearity,Operationalist}` | `cstz.axioms` | `check_profile_linearity`, `check_eval_linearity`, `check_operationalist`, `check_bilinearity` | **P1, P2, P3** | (via `test_verification.py`) |
| 3 | Framework | `CSTZ.Framework` + `Framework/{Discriminator,Profile,FourCell,XOR,Regime,Membership,RegimeReadWrite}` | `cstz.framework` | `profile`, `CellKind`, `classify`, `chi`, `is_residue`, `evolve`, `Regime` | — | `test_framework.py` |
| 4 | Sets | `CSTZ.Sets` + `Sets/{Extensionality,Russell,Foundation,SymmetricDifference,Pairing,PowerSet,Infinity,Choice,BooleanDimensions}` | `cstz.sets` | `kappa_equiv`, `russell_exclusion`, `is_paired`, `sym_diff_discriminator` | **P7** | `test_sets.py` |
| 5 | Homotopy | `CSTZ.Homotopy` + `Homotopy/{Simplicial,ChainComplex,Exhaustivity,Groupoid,Univalence,SelfInverse}` | `cstz.homotopy` | `chain_complex_check`, `exhaustive_filling`, `self_inverse_check` | **P5, P6** | `test_homotopy.py` |
| 6 | Category | `CSTZ.Category` + `Category/{Directed,TwoCell,Functor,NaturalTrans,Adjunction,Yoneda,Limits,Emergent}` | `cstz.category` | `DirectedMorphism`, `compose_witnesses`, `interchange`, `LimitKind` | **P8** | `test_category.py` |
| 7 | Higher categories | `CSTZ.Higher` + `Higher/{InfinityOne,Triangle,Perspective,Toroid,FreeNK}` | `cstz.higher` | `Perspective` enum, `rotate`, `triangle_identity` | — | `test_higher.py` |
| 8 | Monoidal | `CSTZ.Monoidal` + `Monoidal/{Tensor,Symmetric,Delooping,CayleyDickson,InternalHom,CartesianClosed,Coherence}` | `cstz.monoidal` | `tensor_witness`, `cd_mul`, `swap_conjugation` | — | `test_monoidal.py` |
| 9 | Topos | `CSTZ.Topos` + `Topos/{SelfEnriched,SubobjectClassifier,Fibered,ProofTheory,FOL,SelfHosting,FixedPoint,Irremovable,Sheaves,Fano,Convergence}` | `cstz.topos` | `omega_neg`, `omega_conj`, `omega_disj`, `FANO_POINTS`, `FANO_LINES`, `verify_fano_line`, `unique_top_form` | — | `test_topos.py` |
| 10 | Examples | `CSTZ.Examples` + `Examples/{GF2Cubed/*, TruthTables}` | `cstz.examples` | `POPULATION`, `e1`, `e2`, `e3`, `eval_dot`, `kappa_0..kappa_n` | — | `test_examples.py` |
| 11 | Meta | `CSTZ.Meta.TechniqueProfile` | *N/A — Agda-only metadata* | — | — | — |
| V  | Verification | `CSTZ.Verification.{Segal,RISC,CDHexagons,ChoiceBounds,BilinearPairings,FixedPointStability,ChainBound,OmegaChains,AnnihilatorClosure,MonoidalCoherence,ExhaustiveLimits}` | `cstz.verification` | `check_boundary_squared`, `check_boundary_squared_all`, `check_fano_lines`, `check_risc`, `check_cd_commutativity`, `check_fixed_point_stability`, `check_swap_involutive`, `check_profile_linearity_exhaustive`, `check_eval_linearity_exhaustive`, `check_truth_tables` | **P9** | `test_verification.py` |

## 3. Postulate catalog

Every `postulate` block in `agda/CSTZ/`, enumerated. The "Runtime check"
column names a function in `src/cstz/` that empirically verifies the
property on finite inputs (dash = no computational counterpart, the
postulate is purely structural).

| ID | File:line | Name | Informal statement | Runtime check |
|----|-----------|------|--------------------|---------------|
| P1 | `agda/CSTZ/Axiom/ProfileLinearity.agda:26` | `profile-linearity` | `eval (d₁ +V d₂) a ≡ eval d₁ a +F eval d₂ a` | `cstz.axioms.check_profile_linearity`; exhaustive at n via `cstz.verification.check_profile_linearity_exhaustive` |
| P2 | `agda/CSTZ/Axiom/EvalLinearity.agda:27` | `eval-linearity` | `eval d (y₁ +V y₂) ≡ eval d y₁ +F eval d y₂` | `cstz.axioms.check_eval_linearity`; exhaustive via `cstz.verification.check_eval_linearity_exhaustive` |
| P3 | `agda/CSTZ/Axiom/Operationalist.agda:26` | `operationalist` | no discriminator separates `a`, `b` ⇒ `a ≡ b` | `cstz.axioms.check_operationalist` (checks the antecedent; conclusion is the axiom) |
| P4 | `agda/CSTZ/Exterior/Boundary.agda:88` | `∂∘∂≡0` | `∂ (∂ f) t ≡ 𝟘` for every exterior element | `cstz.verification.check_boundary_squared` (all basis elements); `check_boundary_squared_all` (all 2^(2^n) elements, exhaustive at n=3) |
| P5 | `agda/CSTZ/Homotopy/Exhaustivity.agda:41` | `leibniz` | graded Leibniz for `∂` on a `·F`-product (placeholder type) | — |
| P6 | `agda/CSTZ/Homotopy/Exhaustivity.agda:48` | `exhaustive-filling` | every cycle `R` admits a filling `C` in the extended space | — |
| P7 | `agda/CSTZ/Sets/Foundation.agda:73` | `chain-depth-bound` | `depth ≤ n` for any ∈-chain in `GF(2)^n` | — (mathematically tied to `check_risc`, `check_fixed_point_stability`) |
| P8 | `agda/CSTZ/Category/Yoneda.agda:58` | `a≡b` (local) | closes `yoneda-faithful` pending operationalist/finiteness | — |
| P9 | `agda/CSTZ/Verification/ChainBound.agda:49` | `chain-bound` | any chain of depth `k` in `GF(2)^n` satisfies `k ≤ n` | — (consistent with P7) |

Line numbers above point to the declaration line (not the surrounding
`postulate` keyword). They are produced mechanically by
`scripts/count_postulates.py`, which strips Agda's nestable block
comments and line comments, then walks each file tracking indent levels
to distinguish block-style `postulate` headers from inline
`postulate <decl>` forms and continuation lines. Re-running the script
is the canonical way to verify this table:

```
$ python3 scripts/count_postulates.py
agda/CSTZ/Axiom/EvalLinearity.agda:27    eval-linearity
agda/CSTZ/Axiom/Operationalist.agda:26   operationalist
agda/CSTZ/Axiom/ProfileLinearity.agda:26 profile-linearity
agda/CSTZ/Category/Yoneda.agda:58        a≡b
agda/CSTZ/Exterior/Boundary.agda:88      ∂∘∂≡0
agda/CSTZ/Homotopy/Exhaustivity.agda:41  leibniz
agda/CSTZ/Homotopy/Exhaustivity.agda:48  exhaustive-filling
agda/CSTZ/Sets/Foundation.agda:73        chain-depth-bound
agda/CSTZ/Verification/ChainBound.agda:49 chain-bound
---
Total postulate declarations: 9
Files scanned: 97
```

Only P1–P4 have first-class computational witnesses in Python. P5–P9
remain structural assumptions in Agda, justified in the paper's
Appendix B.

## 4. Python-only extensions

Each subsystem below is anchored to specific rows of §2.

### `cstz.observe` — witness logging
Defines `Observation`, `Patch`, and `ObservationState`. Pins to row 3
(Framework) and row 9 (Topos): every observation is a discrimination, and
a `Patch` is the runtime carrier of the four-cell Ω algebra from
`cstz.topos`. Enforces four invariants — S₃ symmetry, operationalist
equivalence (computed at query time), regime monotonicity, profile
accumulation by OR — that make `ObservationState` the runtime analogue of
the sheaf of discriminations described in `CSTZ.Topos.Sheaves`.
Exercised by `tests/test_observe.py`.

### `cstz.classify/` — τ-identity classifier engine
Three layers, all pinned to row 3 (Framework/Discriminator):

- `classify/registry.py` — `DiscriminatorRegistry`: stable global vocabulary; each discriminator has a one-hot bitvector ID, a semantic contract, a pure `fires()` predicate, and a version. Stability is what makes z-path equivalence well-defined.
- `classify/base.py` — abstract `Classified` (τ bitmask + `ShapeWitness`).
- `classify/pyast.py`, `classify/bytes.py`, `classify/toy.py` — concrete classifiers over Python ASTs, byte streams (Morton-interleaved keys), and toy fixtures. Pure, idempotent, context-free.
- `classify/walker.py`, `classify/adapter.py` — compose τ along z-paths (self-delimiting traversal coordinates) and emit to `Patch`. Walker monotonicity prevents retroactive rewrites.

No Agda counterpart because classification is a *runtime* concern —
the Agda formalization fixes the algebra of discriminators but does not
describe how to obtain them from a concrete syntax tree.

### `cstz.projections.pff_json` — PFF serializer
Pins the `ObservationState` runtime to `rhpf-pff-profiles/pff.schema.json`.
Emits six sections: `ranks` (one per regime step), `patches` (one per
`Patch`), `charts` (one per (discriminator, perspective) pair),
`addresses0` (grade-0 cells per observed element), `paths1`
(operationalist-equivalence glue), `paths2` (computed on demand).

### `cstz.legacy/` — superseded stack
`agda_synth.py`, `byte_classifier.py`, `core.py`, `pff.py`,
`pff_cascade.py`, `pff_python_classifier.py`, `python_classifier.py`.
Still importable but excluded from the coverage gate:
`pyproject.toml` declares
```toml
[tool.coverage.report]
fail_under = 100
omit = ["src/cstz/legacy/*"]
```
These modules correspond to the earlier SPPF/PFF formulation documented
in the root-level `inference.agda`, not to the phased `agda/CSTZ/`
hierarchy.

## 5. Root-level Agda artifacts

- `inference.agda` — standalone SPPF reference (submodules `GF2`,
  `UnionFind`, `Fiber`, `Kappa`, `Eta`, `Cleavage`, `CellObs`, `Core`,
  `Ingest`, `Huffman`, …). Pre-dates the `agda/CSTZ/` phased hierarchy
  and is the metamathematical reference for the code in `cstz.legacy/`.
- `CoreProof.agda` — generated proof witness for a specific 7,500-node
  AST (σ = 2,096; τ = 859; κ = 779; 103 η-merges; 7 case splits). Not
  reusable theory; cite as the existence proof that SPPF processing is
  tractable at production scale.

## 6. Navigation &amp; build

**Agda.** Type-check the whole formalization with

```
agda --safe agda/CSTZ/All.agda
```

Dependency: `standard-library-2.1` (declared in `agda/cstz.agda-lib`).
`All.agda` imports every phase in source order, so a clean check
validates rows 1–V of §2 together.

**Python.** No CLI and no `[project.scripts]` in `pyproject.toml`; the
usage surface is the test suite.

```
pytest
```

runs `tests/test_*.py` under a 100 % branch-coverage gate
(`pyproject.toml` lines 21–26: `[tool.coverage.report]` with
`fail_under = 100` and `omit = ["src/cstz/legacy/*"]`).

## 7. Reading order for newcomers

1. Paper §§1–3 in `Topos-Theoretic Grammar Induction and PRNG.md`.
2. Row 1 of §2 (GF(2), Vec, Exterior) → `cstz.gf2`, `cstz.exterior`;
   open `tests/test_gf2.py` and `tests/test_exterior.py` alongside.
3. Side-trip: §3 entries P1–P3 → `cstz.axioms`; and P4 →
   `cstz.verification.check_boundary_squared`.
4. Row 3 (Framework) → `cstz.framework`; then §4 `cstz.observe` for
   the runtime witness model before proceeding to Sets/Homotopy.
5. Rows 4–5 (Sets, Homotopy) with `tests/test_sets.py`,
   `tests/test_homotopy.py`.
6. Rows 6–9 (Category, Higher, Monoidal, Topos) with their tests.
7. Row 10 (Examples) — concrete GF(2)³ walkthrough.
8. §4 `cstz.classify/` — the only heavy Python subsystem with no Agda
   twin; read `registry.py` → `base.py` → (`pyast.py` or `bytes.py`) →
   `walker.py` → `adapter.py` in that order.
9. §4 `cstz.projections.pff_json` + `rhpf-pff-profiles/pff.schema.json`.
10. Optional deep dives: §5 `inference.agda`, `CoreProof.agda`, and
    `cstz.legacy/` for historical context.
