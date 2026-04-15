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
| P1 | `agda/CSTZ/Axiom/ProfileLinearity.agda:34` | `profile-linearity` | `eval (d₁ +V d₂) a ≡ eval d₁ a +F eval d₂ a` | `cstz.axioms.check_profile_linearity`; exhaustive at n via `cstz.verification.check_profile_linearity_exhaustive` |
| P2 | `agda/CSTZ/Axiom/EvalLinearity.agda:36` | `eval-linearity` | `eval d (y₁ +V y₂) ≡ eval d y₁ +F eval d y₂` | `cstz.axioms.check_eval_linearity`; exhaustive via `cstz.verification.check_eval_linearity_exhaustive` |
| P3 | `agda/CSTZ/Axiom/Operationalist.agda:38` | `operationalist` | no discriminator separates `a`, `b` ⇒ `a ≡ b` | antecedent: `cstz.axioms.check_operationalist`; conclusion constructively realized by `cstz.sets.kappa_equiv` (regime sweep) and `cstz.sets.is_paired` (residue + annihilator) |
| P4 | `agda/CSTZ/Exterior/Boundary.agda:95` | `∂∘∂≡0` | `∂ (∂ f) t ≡ 𝟘` for every exterior element | `cstz.verification.check_boundary_squared` (all basis elements); `check_boundary_squared_all` (all 2^(2^n) elements, exhaustive at n=3) |
| P5 | `agda/CSTZ/Homotopy/Exhaustivity.agda:46` | `leibniz` | graded Leibniz for `∂` on a `·F`-product (placeholder type) | — |
| P6 | `agda/CSTZ/Homotopy/Exhaustivity.agda:53` | `exhaustive-filling` | every cycle `R` admits a filling `C` in the extended space | — |
| P7 | `agda/CSTZ/Sets/Foundation.agda:77` | `chain-depth-bound` | `depth ≤ n` for any ∈-chain in `GF(2)^n` | — (mathematically tied to `check_risc`, `check_fixed_point_stability`) |
| P8 | `agda/CSTZ/Category/Yoneda.agda:65` | `a≡b` (local) | closes `yoneda-faithful` pending operationalist/finiteness | — |
| P9 | `agda/CSTZ/Verification/ChainBound.agda:53` | `chain-bound` | any chain of depth `k` in `GF(2)^n` satisfies `k ≤ n` | — (consistent with P7) |

Line numbers above point to the declaration line (not the surrounding
`postulate` keyword). They are produced mechanically by
`scripts/count_postulates.py`, which strips Agda's nestable block
comments and line comments, then walks each file tracking indent levels
to distinguish block-style `postulate` headers from inline
`postulate <decl>` forms and continuation lines. Re-running the script
is the canonical way to verify this table:

```
$ python3 scripts/count_postulates.py
agda/CSTZ/Axiom/EvalLinearity.agda:36    eval-linearity
agda/CSTZ/Axiom/Operationalist.agda:38   operationalist
agda/CSTZ/Axiom/ProfileLinearity.agda:34 profile-linearity
agda/CSTZ/Category/Yoneda.agda:65        a≡b
agda/CSTZ/Exterior/Boundary.agda:95      ∂∘∂≡0
agda/CSTZ/Homotopy/Exhaustivity.agda:46  leibniz
agda/CSTZ/Homotopy/Exhaustivity.agda:53  exhaustive-filling
agda/CSTZ/Sets/Foundation.agda:77        chain-depth-bound
agda/CSTZ/Verification/ChainBound.agda:53 chain-bound
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

## 8. Cofibration of Agda ↔ Python

The Agda specification and the Python runtime implement the same theory
but make different definitional choices. Treating each side as a set of
named objects and asking, concept by concept, *"what is its status on
the other side?"* exposes a **cofibration**: the two implementations
share a common subtheory, but each carries a *cofiber* of concepts the
other side treats only implicitly or not at all.

Every concept is placed in one of nine status cells. **E** = explicitly
named; **I** = implied (derivable from other named code but not itself
named); **M** = missing.

| status | Agda **E** | Agda **I** | Agda **M** |
|--------|------------|------------|------------|
| **Python E** | aligned (may still differ in *proof strength*) | Python names a derived fact | Python-only |
| **Python I** | Agda names it; Python derives it | both implicit (outside this study) | — |
| **Python M** | Agda-only | — | — |

The table below and the three subsections distill the mechanical
enumeration in each phase to the mismatched cells only; trivial
name-casing differences (e.g. Agda `cd-mul` ↔ Python `cd_mul`) are
aligned and omitted. Verified by spot-checking `topos.py:19–22`,
`higher.py:14–24`, `category.py:19`, `agda/CSTZ/Category/Directed.agda:27`,
and `agda/CSTZ/Topos/Fano.agda:54–80`.

### 8.1 Uniform proofs vs. parameterized proof-schemas

These are **E/E** cells where the concept is named on both sides, but
the Agda form is a structural axiom or theorem quantified over every
dimension `n`, while the Python form is an exhaustive check at a
caller-chosen `n`. These are the most subtle asymmetries because a
casual reader may read "empirical check" as "weaker evidence" — under
the operationalist axiom (P3) it is not.

**Exhaustion is proof, under operationalism.** The operationalist axiom
— "if no discriminator separates `a` and `b`, then `a ≡ b`" — *defines*
identity in this framework to be operational. Consequently every
well-formed property is automatically ≡-invariant (it is built from
discriminators, which are exactly the operations that ≡ preserves). At
a fixed dimension `n` the population `GF(2)ⁿ` is finite, so an
exhaustive check over the finite population is a proof of the property
*at that dimension*, with operationalist consistency supplying
universality within the logical framework: no "hidden" counterexample
can exist outside what discriminators can see. The genuine asymmetry is
therefore not "test vs. proof" but **uniform vs. parameterized**:
Agda's postulate (or derivation from postulates) is one statement
covering all `n`; Python's `check_*_exhaustive(n)` is a family of
proofs indexed by `n` — a complete proof for every concrete `n` the
caller chooses, but not a single statement quantified over `n`.

| Concept | Agda form | Python form | Refined mismatch |
|---------|-----------|-------------|------------------|
| profile linearity (P1) | `postulate profile-linearity` (`Axiom/ProfileLinearity.agda:34`) — uniform in n | `axioms.check_profile_linearity` + `verification.check_profile_linearity_exhaustive(n)` | uniform proof ↔ proof-schema parameterized by n |
| eval linearity (P2) | `postulate eval-linearity` (`Axiom/EvalLinearity.agda:36`) — uniform in n | `axioms.check_eval_linearity` + exhaustive variant | same |
| operationalist (P3) | `postulate operationalist` (`Axiom/Operationalist.agda:38`) — propositional equality `a ≡ b` coincides with operational indistinguishability | `sets.kappa_equiv` (`sets.py:22`) **and** `sets.is_paired` (`sets.py:67`) — *constructively realize* the equivalence relation: `kappa_equiv` sweeps every `d ∈ regime` and checks `eval(d,a) == eval(d,b)`; `is_paired` computes the residue `a ⊕ b` and transposes it to the surface of each discriminator via the annihilator check `dot(d, a ⊕ b) == 0` (equivalent formulation: the residue is annihilated by every k-regime's measurement) | aligned — Python defines ≡ operationally at each (regime, a, b); the only residual difference is substitutability, which Agda inherits automatically from propositional `≡` while Python requires the caller to invoke `kappa_equiv` at each comparison site |
| ∂∘∂ ≡ 0 (P4) | `postulate ∂∘∂≡0` (`Exterior/Boundary.agda:95`) — uniform in n | `verification.check_boundary_squared` (all basis) + `_all` (exhaustive at n=3: all 2^(2ⁿ) elements) | uniform proof ↔ proof-schema; `_all` at n=3 is a proof at n=3, not weaker evidence |
| Fano lines | 7 theorems `fano-line-1..7` (`Topos/Fano.agda:54–80`) | `FANO_LINES` list + `verify_fano_line` | **no proof-strength mismatch** — the Fano plane has exactly 7 lines over GF(2); enumerating and checking them is the same proof, expressed differently |
| DNE / EM-fail | `dne`, `em-fails-at-gap` (`Topos/ProofTheory.agda:27–31`) | `topos.dne`, `check_truth_tables` | **no mismatch** — the four-valued Ω has a finite truth table; exhaustion is universal |

The Agda-only gap is therefore narrower than it first appears: for
P1, P2, P4, Fano, and DNE the Python side can produce a proof at any
specific `n` the user asks for, with the same confidence as a uniform
proof — it just does not produce one statement quantified over `n`.
P3 is *not* the separate "foundational" gap my earlier draft claimed.
It is constructively realized by `sets.kappa_equiv` (regime sweep) and
`sets.is_paired` (residue-plus-annihilator), both of which *compute*
the equivalence relation `≡` rather than merely checking the axiom's
hypothesis. The only residual asymmetry is *substitutability*: in Agda
a proof of `a ≡ b` propagates through every context automatically; in
Python the equivalence must be invoked at each comparison site (a
caller who writes `a == b` gets structural equality, not `≡`).

### 8.2 The Agda cofiber (explicit in Agda, missing or implied in Python)

**Structural types and records Python inlines.**
- `DiscSystem`, `DiscPair` records (`Framework/Discriminator.agda:37,69`) — Python encodes discriminators as integer bitmasks without a wrapping type; a `DiscriminatorRegistry` exists in `classify/registry.py` but is a runtime catalogue, not an algebraic object.
- `Adjunction` record + `Axis` data (`Category/Adjunction.agda:40,59`) — **no Python counterpart**; adjunctions are implicit in `compose_witnesses` / `compose_coeff` usage.
- `LinearFunc` (`Vec.agda:66`), `Exterior` (`Exterior/Basis.agda:81`) — Python uses bare `int` and `list[int]` respectively.

**Postulate spine without Python witnesses** (see §3 for the full catalog).
- P5 `leibniz`, P6 `exhaustive-filling` (`Homotopy/Exhaustivity.agda`)
- P7 `chain-depth-bound` (`Sets/Foundation.agda`)
- P8 `a≡b` local to `yoneda-faithful` (`Category/Yoneda.agda:65`)
- P9 `chain-bound` (`Verification/ChainBound.agda`)

**Enumerated constructions Python condenses to a single verifier.**
- Fano lines: seven separate theorems in Agda ↔ one `verify_fano_line` predicate in Python (see also §8.1).
- Segal coherence: `top-3-cell` plus six face definitions in `Verification/Segal.agda` ↔ no Python counterpart (Segal structure is implicit).
- Truth-table coverage: `neg-gap`, `neg-overlap`, `dne-gap`, `dne-overlap`, `conj-gap-any`, `disj-gap-gap`, `em-gap`, `em-overlap`, `expl-overlap` (nine named cases in `Examples/TruthTables.agda`) ↔ one `check_truth_tables` function that bundles the cases.

**Agda-only metadata.**
- `Meta/TechniqueProfile.agda` — proof-technique annotations (Appendix D); Python has no analogue and does not need one (the metadata describes the Agda development itself).

### 8.3 The Python cofiber (explicit in Python, missing or implied in Agda)

**Runtime subsystems with no Agda counterpart at all.**
- `cstz.observe` — `Observation`, `Patch`, `ObservationState` (a runtime sheaf of discriminations). Agda's sheaf axioms are in `Topos/Sheaves.agda`; the *state carrier* that accumulates observations at runtime is Python-only.
- `cstz.classify/` — `DiscriminatorRegistry`, `Classified`, `Walker`, `Adapter`, plus three concrete classifiers (`pyast`, `bytes`, `toy`). Classification maps concrete syntax to discriminator bitmasks; the Agda formalization fixes the algebra of discriminators but does not prescribe how to obtain them.
- `cstz.projections.pff_json` — serializer to `rhpf-pff-profiles/pff.schema.json`; no mathematical counterpart.
- `cstz.legacy/` — superseded SPPF/PFF stack; mirrors `inference.agda` (the older standalone Agda spec), not `agda/CSTZ/`.

**Algebra Python names that Agda treats structurally.**
- Ω constants `TRUE_OMEGA`, `FALSE_OMEGA`, `UNKNOWN_OMEGA`, `OVERDET_OMEGA` (`topos.py:19–22`) — Agda reasons about these values through `Topos/ProofTheory.agda` without giving them individual names (they appear as pattern-match cases).
- Ω operators `omega_neg`, `omega_conj`, `omega_disj` (`topos.py:25–…`) — Agda has the *properties* (`em-fails-at-gap`, etc.) but not the operators as first-class functions; they are implicit in the sub-object classifier's algebra.
- `Perspective` IntEnum (`higher.py:14`, members `KAPPA`, `SIGMA`, `TAU`) and toroid-point constants `TAU_POINT`, `SIGMA_POINT`, `KAPPA_POINT` (`higher.py:22–24`) — Agda uses structural role tracking without an enum type.

**Bundled convenience checks.**
- `axioms.check_bilinearity` (`axioms.py:28`) — Agda derives bilinearity from P1 ∧ P2 by composition; Python names the conjunction.
- `verification.check_truth_tables` (`verification.py:93`) — collapses Agda's nine truth-table theorems into a single sweep (also noted in §8.2).

### 8.4 Summary table

| Direction | Cardinality (indicative) | Notable examples |
|-----------|--------------------------|------------------|
| E/E aligned (same statement, same strength) | ~49 | `cd_mul`, `rotate`, `dot`, `basis`, `classify`, `evolve`, `russell_exclusion`, `DirectedMorphism`, `LimitKind`, Fano lines, DNE, **P3 operationalist via `kappa_equiv`/`is_paired`** |
| E/E uniform vs. parameterized schema (§8.1) | 3 | P1, P2, P4 — Agda uniform in n; Python proof per caller-chosen n |
| E/E substitutability caveat | 1 | P3 — `≡` propagates automatically in Agda's propositional equality; Python callers must invoke `kappa_equiv` at each comparison site |
| Agda E, Python M/I (§8.2) | ~15 | `DiscSystem`, `Adjunction`, P5–P9 postulates, Segal cells, truth-table cases |
| Agda M/I, Python E (§8.3) | ~20 (plus all of `classify/`, `observe`, `projections`) | Ω constants, Ω operators, `Perspective`, `check_bilinearity`, classification engine |

### 8.5 Regenerating this section

The postulate spine (§3) is mechanical:
```
python3 scripts/count_postulates.py
```
The full named-object enumeration used here was produced by scanning
each phase's modules for `data`/`record`/`postulate`/typed-name openings
in Agda and for `class`/`def`/upper-snake constants in Python. A
generalized `scripts/collect_decls.py` would automate re-running the
cofibration; until then, the hand enumeration is auditable by
re-grepping each cited file and comparing against this section.
