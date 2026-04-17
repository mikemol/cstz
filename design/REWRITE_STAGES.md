# scripts/closed_loop.py — staged rewrite plan

Each stage is a small committable unit.  Stop and commit after every
stage; subsequent sessions can pick up from any checkpoint.  Do not
attempt to write stages 1-N in one session unless context budget is
clearly sufficient.

## Stage 0: Prerequisites (DONE)

SPPF principles + decisions pinned:

- `p-type-theory-everywhere`, `p-extensionality-via-hit`
- `p-self-similarity`, `p-embarrassingly-parallel`
- `p-maximal-freedom`, `p-kappa-is-derived-xor`, `p-atoms-are-formal-tau-sigma-channels`
- `d-python-class-hierarchy-for-k`, `d-tausigma-type-preserves-constraint`
- `d-state-is-merge-friendly`, `d-disk-as-merge-protocol`
- `d-wedge-combinator-general-exterior-algebra`
- `d-articulation-scorer-pluggable`, `d-weight-objective-pluggable`
- `d-report-is-full-state-jsonl`

## Stage 1: Type core (~200 lines)

Inductive + algebraic types only; no I/O, no algorithms.

- `TauSigma` — frozen dataclass, `tau: int`, `sigma: int`, `kappa` property.
- `S3` — frozen dataclass wrapping a permutation of `(0, 1, 2)`.
  Group composition, action on `TauSigma`.
- `K` — abstract base class; subclasses `Atom(key: str)` and `Wedge(a: K, b: K)`.
  Structural equality by default (dataclass eq).
- `Thing` — frozen dataclass; `id: str`, `display: str`, `source_path: str`,
  τ/σ bitmasks over the K-pool by bit-index.
- `Pool` — ordered mapping of K-key → (K, bit_index).  Append-only.

Smoke test: import module, instantiate one of each type, print, verify
κ = τ ⊕ σ invariant holds after S3 action.  Commit.

## Stage 2: State + merge/restrict (~100 lines)

- `State` — frozen dataclass holding `Pool`, `things: dict[str, Thing]`,
  `oracle_pairs: frozenset`, `iteration: int`, `trajectory: tuple`.
- `State.merge(other)` — union pools (dedupe by K key); union things;
  union oracle pairs; concatenate trajectory.
- `State.restrict(things=..., k_pool=...)` — sub-state with requested slice.
- `State.signature()` — hash for fixed-point detection.

Smoke test: merge two small states; verify associativity on a trivial case.
Commit.

## Stage 3: Atom extraction (~150 lines)

Pool every top-level declaration from all three sources; for each,
compute verbatim kind-string set from subtree; populate τ = σ as the
set-membership bitmap.

- Re-use `scripts/structural_identity.py` parsers (don't rewrite).
- One `extract_initial_state(repo: Path) -> State` entrypoint.
- All decls in one flat thing-pool.
- Source provenance appended as a K observable ("source:paper" etc.)
  per `p-source-is-a-k`.

Smoke test: call on repo root; assert `len(state.things) == ~700`,
`len(state.pool) == ~some_number`, κ = 0 for all atoms initially.
Commit.

## Stage 4: Scorer + objective protocols (~50 lines)

Type aliases and a small built-in registry.

- `Scorer = Callable[[State, K, K], float]`
- `Objective = Callable[[State], float]`
- Default scorer: four-cell entropy of (K_i, K_j) across things.
- Default objective: sum over oracle pairs of `popcount(τ_A & ~σ_B) *
  popcount(~τ_A & σ_B)` (Boolean-earning witness count).

Smoke test: default scorer/objective run on small state; produce sane
scalars.  Commit.

## Stage 5: step() (~200 lines)

Pure function, no mutation.

- Accumulate Belnap evidence (lazy / on-demand computation from τ/σ masks).
- Evaluate candidate wedges among top-scoring K-pairs under configured scorers.
- Propose wedges whose score exceeds threshold; register as Wedge(A, B) K's;
  append bits to pool; extend thing bitmaps with AND-of-parents.
- Gradient-step weights using configured objective.
- Append trajectory record.

Smoke test: run step() once on the initial state; assert pool grows, state
signature changes, trajectory has one record.  Commit.

## Stage 6: Fixed-point driver (~50 lines)

- `run(state, scorers=..., objectives=...) -> State`:
  loop step() until signature stable for N consecutive iterations
  (N configurable; default 2).  No max iterations.

Smoke test: run on a tiny 5-thing subset; assert it terminates.  Commit.

## Stage 7: split into 7.0 (eager-numpy refactor) + 7.1 (I/O)

Actual work through 7.0.8 has been the eager-numpy refactor required
to make State merge-friendly for Stage 7.1 and parallel-shard-friendly
for Stage 10.  The original "append-only JSONL I/O" target is Stage
7.1 and has not landed yet.

### Stage 7.0 — eager-numpy substages (LANDED)

- 7.0    — initial conversion of Thing.tau_mask / sigma_mask from
           Python int bitmasks to np.ndarray(dtype=bool).
- 7.0.5  — numpy fast paths applied in _count_four_cell + step()
           (BLAS matmul for candidate-pair enumeration).
- 7.0.6  — Thing._hash cache reverted (signature() comparison uses
           __eq__, never hash()); termination switched to trajectory
           signal per d-fixed-point-is-termination.
- 7.0.7a — Pool internal representation = structured-dtype numpy
           array (POOL_DTYPE); O(1) bit_of via _key_to_bit cache.
           Enacts l-pool-as-structured-dtype-array.
- 7.0.7b — State.things → parallel (thing_ids, tau_masks, sigma_masks)
           arrays; firing_bitmaps_of(state) returns .tau_masks.T as
           an O(1) view.  Enacts l-state-things-as-parallel-arrays.
- 7.0.7c — Wedge-batch dedup via np.unique on canonical keys.  Enacts
           l-hash-consing-as-np-unique.
- 7.0.8  — oracle_pair_indices cache (Int[n_pairs, 2]); scorer /
           objective hot paths vectorized; Thing.remap +
           _compute_firing_bitmaps shim retired.  Enacts
           l-oracle-pairs-as-index-array.  Resolves Stage 7 audit
           Severity 1 + 2.
- 7.0.9  — trajectory is TRAJECTORY_DTYPE structured numpy array
           (7 mandatory numeric fields) + parallel trajectory_aux
           tuple-of-dicts for optional scorer/objective structural
           identity.  run_to_fixed_point termination reads
           trajectory[-1]['articulated_count'] as a typed field —
           typos fail dtype validation instead of silently returning
           .get() default.  Thing docstring rewritten to reflect its
           post-7.0.7b value-type role (not primary storage).  New
           principle p-set-algebra-and-tensor-reduction-use-distinct-
           forms pins the emergent "authoritative + numpy cache"
           pattern across Pool, State.thing_ids, State.oracle_pairs,
           State.trajectory.  Enacts l-trajectory-as-structured-dtype-
           array.  Resolves Stage 7 audit post-7.0.8 Severity 2.
- 7.0.10 — five scorer classes → CellScorer(cells, reduce) factoring:
           CellExtractor (ThingsFourCell, OracleSixteenCell) × Reducer
           (SumOffDiagonal, LogProductOffDiagonal, ShannonEntropy,
           SelectCell(idx)).  Singletons written via functools.partial
           currying (on_things, on_oracle_pairs).  Enacts
           l-scorer-as-shape-contract.  Net LOC: -78.
- 7.0.11 — _count_four_cell vectorized off state.tau_masks columns;
           signature takes bit indices (state, i: int, j: int, ...)
           rather than K objects.  Slow path no longer iterates
           state.things (no Thing reconstruction).  Resolves post-
           7.0.10 Stage 7 audit Severity 1 + 2 (K-object roundtrip
           in _count_four_cell).
- 7.0.12 — Tier 1 of the S3-cluster: S3.act_on_tsk operates on
           (3, ...) bool tensors (enacts l-s3-as-axis-permutation);
           POOL_DTYPE gains orbit_id + orbit_parent fields (trivial
           self-reference for current symmetric regime);
           pool_has_trivial_orbits + sigma_derivable_from_tau probes
           (independent signals for Stage 7.1 — orbit-structure
           serialization is conditional on the former, sigma_masks
           storage is conditional on the latter).  Pure refactor +
           schema-forward-compat for Tier 2/3.  No activation of the
           asymmetric regime.  Post-audit fixes: direct-Python S3.act
           for the scalar case (no tensor materialization);
           is_symmetric split into the two probes above.
- 7.0.13 — Tier 2 of the S3-cluster: Rotated(base, perm) K subclass
           alongside Atom/Wedge/ZeroK; top-level swap(k) and
           rotate(k, g) helpers.  Pool.with_k propagates orbit_id
           (root) + orbit_parent (immediate) for Rotated K's;
           Atom/Wedge/ZeroK remain self-orbit.  Enacts
           l-k-level-s3-operators as scaffolding only — semantic
           switch (step() articulating Rotated K's) deferred to
           Tier 3 post-Stage-7.1.  Supplement: compose(k1, k2, g)
           helper + wedge-normalize generalized for Rotated leaves
           (distinct-leaves-count nilpotency) + K ∧ 0 = 0 absorption
           bug fixed.

### Stage 7.1 — hybrid JSONL + HDF5 I/O (LANDED)

dump_state / load_state partitioned per p-storage-matches-data-shape:
small-algebra authoritative forms to JSONL (initially pool.jsonl,
things.jsonl, oracle_pairs.jsonl, weights.jsonl, trajectory_aux.jsonl);
bulk tensor caches to HDF5 (state.h5 with /masks/tau, optional
/masks/sigma, /trajectory compound dtype).  Sigma masks conditional on
state.sigma_derivable_from_tau; loader reconstructs σ = τ when absent.
k_from_structure closes the p-bijective-hash-consing round-trip.
Enacts l-hdf5-compound-dtypes-mirror-in-memory.  Nine of ten lemmas
enacted; only l-combinator-and-s3-operators-are-equivalent remains
active (Tier 3 scope).

#### Stage 7.1.1 — pool to HDF5; chunked + extensible; algebraic self-validation

Closes the post-7.1 audit's three Severity-2 + Severity-3 items:
  - Pool migrates from pool.jsonl to /pool/keys_array as an HDF5
    compound dataset (POOL_HDF5_DTYPE with S512 'key' bytes).
    Aligns to l-hdf5-compound-dtypes-mirror-in-memory's "pool and
    masks share pool_size attribute on parent group" formulation.
  - All HDF5 datasets are now chunked with maxshape supporting
    axis-0 growth (axis-1 also for masks); readiness for Stage-10
    incremental shard accumulation.
  - Validation via algebra-derived expectations rather than
    range-checks: orbit_id checked against K-structure-derived
    expectation (walk Rotated chain → pool.bit_of(root)); trajectory
    iteration field checked for consecutive monotonicity
    (np.array_equal vs np.arange(1, n_iter+1)).
  - JSONL retirement direction ratified: pool.jsonl gone; remaining
    JSONL files (things, oracle_pairs, weights, trajectory_aux) are
    transitional, slated for migration.
  - SCHEMA_VERSION bumped to 7.1.1.

#### Stage 7.1.2 — Tier 3 activation: general combinator on Rotated-parent wedges

Enacts l-combinator-and-s3-operators-are-equivalent (10/10 lemmas
now enacted).  Closes the post-7.1.1 audit's Sev 3 (c) gap and
activates the asymmetric regime:
  - Sev 3 (c) fix: smoke-test exercises a Pool containing an Atom +
    its swap through full dump/load; orbit metadata round-trips,
    pool_has_trivial_orbits correctly flips False.
  - _articulate_wedges_batch detects Rotated-parent grade-2 wedges
    and computes (τ_W, σ_W) via the strict-GF(2) general
    exterior-algebra combinator (τ_W = (τ_A·σ_B) ⊕ (σ_A·τ_B);
    σ_W = (τ_A·τ_B) ⊕ (σ_A·σ_B)) instead of AND-of-parents.  All-
    non-Rotated wedges keep AND semantics.  Higher-grade Rotated-
    leaf wedges fall back to AND (deferred to future stage).
  - c-d-wedge-combinator-typo-fix clarifies the σ-formula's
    strict-GF(2) reading (symmetric atoms degenerate to 0 in BOTH
    channels, not "σ_K = τ_A·τ_B" as the decision body originally
    said); meaningful asymmetric wedges require at least one
    Rotated parent.
  - Smoke test: rotate two atoms via (τκ) transposition; construct
    asymmetric State; articulate the wedge; verify σ ≠ τ on the
    thing; verify /masks/sigma is genuinely written; round-trip
    preserves the asymmetric firing bit-identically.
  - SCHEMA_VERSION bumped to 7.2.0 (major stays 7 so 7.1.x dumps
    still load).

Non-goals: step()-level demand-driven Rotated articulation (future
stage with a concrete demand-criterion design); grade-3+ recursive
combinator; further JSONL retirement.

### Stage 7.2 → 7.2.2 — post-Tier-3: step()-level asymmetric orbit demands

7.2 initially introduced an eager write-path orbit model
(articulate_rotated_from_residue + run_to_asymmetric_fixed_point +
Pool.with_k_and_orbit).  This was superseded in 7.2.2 by a lazy
read-path syndrome-decoded approach after the algebraic identity
(τ⊕σ)|σ = τ|σ was recognized — meaning virtual orbit probes' τ∪σ
co-fire is IDENTICAL to the base K's, and the 3P×3P virtual matmul
was 9 copies of the base P×P block.

Current (7.2.2+ canonical) model:
  - step() Phase 1: base P×P co-fire matmul on τ∪σ union (same
    cost as pre-7.2).
  - step() Phase 2: for each base candidate pair (i, j), ALSO
    demand Wedge(K_i, Rotated(K_j, g)) for the (τκ) and (σκ) S3
    generators on grade-1 K's.  These Rotated-leaf wedge demands
    are INFERRED from the base co-fire — the algebraic identity IS
    the syndrome; no virtual firing matrix materialized.
  - Rotated-leaf wedges enter pool via _articulate_wedges_batch's
    general combinator branch (Tier 3, grade-2 only).  Their orbit
    is virtual — NOT materialized as separate pool entries.
  - Grade-3+ Rotated-leaf wedges: skipped (uncapturable demand;
    Tarski convergence preserved).
  - No separate orbit-seeding event; no eager mask materialization;
    no plateau detection; no max_plateau_cycles.
  - run_to_fixed_point suffices — no run_to_asymmetric_fixed_point.

Eager model REJECTED: see r-eager-orbit-seeding in rejected.jsonl.

Non-goals (deferred): σ-channel-aware scorer invocation; further
JSONL retirement.

### Stage 7.3 — fire_pair: pool as computation graph; masks as cache

Fundamental architectural shift: the K-pool is a computation graph;
atom mask columns are the primary stored data; all derived K firings
(Wedge, Rotated) are computed lazily via State.fire_pair(k).

  - fire_pair dispatches on K type: Atom → stored column read;
    Rotated → S3 on fire_pair(base); Wedge (all-atom) → AND;
    Wedge (Rotated leaves) → grade-k right-fold / shingling via
    GF(2) cross-term formula.  Memoized per k.key() on State.
  - _articulate_wedges_batch delegates entirely to fire_pair for
    degeneracy checks and column computation.  AND/combinator
    dispatch transparent to callers.
  - Grade-k recursive combinator: right-fold through canonical
    tree's leaves.  Each fold step = one "shingle" from the
    SMR / LFSR framework.  Associativity of exterior product over
    GF(2) ensures right-fold = any bracketing.  det(S) = 0
    collapse = all-zero check (degenerate).

#### Stage 7.3.1 — Belnap-encoded mask matrix

Enacts l-belnap-encoded-mask-matrix: each mask cell carries a 2-bit
Belnap value (populated + fires).  with_pool marks new columns as
gap (⊥); fire_pair-computed columns are populated (T/F).  The type
system distinguishes gap from known-False per p-atoms-gap-preserving.
_count_four_cell migrated to fire_pair (eliminates dual access path).

Non-goals (deferred): ⊤ (contradiction) detection at merge time;
atom-only mask storage (shrinking masks to n_atoms columns).

## Stage 8: CLI (~50 lines)

```
python scripts/closed_loop.py init       # extract atoms, dump initial state
python scripts/closed_loop.py step       # one step on current state
python scripts/closed_loop.py run        # step to fixed point
python scripts/closed_loop.py merge <dirs...>  # merge shard outputs
python scripts/closed_loop.py show <id>  # show one K or Thing
```

Each subcommand reads from `reports/closed_loop/` by default; writes there
on `step`/`run`; accepts `--out-dir` override.  Smoke test: each subcommand
produces valid output.  Commit.

## Stage 9: Full-corpus run + diagnostic views

Run `closed_loop.py run` on the full corpus.  Write small query scripts for
views: Boolean-earning witness cardinality per oracle pair; per-K firing
count; trajectory grade histogram.  These are NOT part of closed_loop.py —
they are separate viewer scripts.  Commit.

## Stage 10: Parallel-shard proof of concept

Two `closed_loop.py run --things-glob ...` invocations in parallel, each
writing to a shard out-dir; a third invocation `merge` loads both and
steps once to reconcile.  Verify that the merged result equals (up to
fixed-point equivalence) the single-process full-corpus result.  Commit.

---

## Discipline

- ONE stage per session unless context is clearly adequate.
- Every stage ends with a smoke test that runs in under 10 seconds.
- Every stage ends with a commit.
- If context pressure rises mid-stage, stop and commit partial progress.
  The next session picks up from the partial commit.
- No stage adds features from a later stage.  Later stages may refine
  earlier code but only in follow-up commits, not inside the current stage.
