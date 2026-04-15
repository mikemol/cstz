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

## Stage 7: Append-only JSONL I/O (~150 lines)

- `dump_state(state, out_dir)` — writes pool.jsonl, things.jsonl,
  belnap.jsonl (sparse non-gap cells only), weights.jsonl,
  trajectory.jsonl.  Append-only.
- `load_state(in_dir)` — concatenate all lines; semantic-merge duplicates
  (sum Belnap counts; union K-pool by key; latest-wins or averaged weights).

Smoke test: dump, load, assert loaded state is equivalent.  Commit.

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
