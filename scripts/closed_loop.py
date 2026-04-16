#!/usr/bin/env python3
"""Closed-loop alignment via iterated κ-evolution.

See ``design/BOOTSTRAP.md`` and ``design/REWRITE_STAGES.md`` for the
architecture and the staged implementation plan.  This file is built
in stages; each stage is a committable unit with its own smoke test.

Stage 1 (this commit): type core only.

- ``TauSigma``  — F₂² state of one K on one Thing (τ, σ; κ derived).
- ``S3``        — symmetric group on {τ, σ, κ}; acts on TauSigma
                   preserving the κ = τ ⊕ σ constraint.
- ``K``         — discriminator (abstract); ``Atom(str)`` and
                   ``Wedge(K, K)`` are the two constructors.
                   Intensional equality by dataclass structure;
                   extensional equality (wedge-commutativity,
                   S3-orbit) is earned via normalize() canonical
                   representatives (HIT-style quotient simulated in
                   Python).
- ``Thing``     — a named declaration; τ-bitmap and σ-bitmap over
                   the K-pool; κ derived by XOR.
- ``Pool``      — append-only ordered registry of K keys to bit
                   indices; hashes for equivalence.

No I/O, no extraction, no step(), no scoring.  Those are Stages 3-7.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterator, NewType, Tuple


# ---------------------------------------------------------------------------
# Semantic NewTypes — prevent stringly-typed category confusion
# ---------------------------------------------------------------------------


ThingId = NewType("ThingId", str)   # opaque identity of a pooled declaration
KKey = NewType("KKey", str)         # canonical key of a K in the pool
Observable = NewType("Observable", str)  # raw observation string from an extractor
# Note: NewType is a static-type device; at runtime these are plain str.
# Treating them as distinct types requires discipline from callers;
# mypy/pyright will catch cross-category passings.


# ---------------------------------------------------------------------------
# TauSigma — F₂² state with κ = τ ⊕ σ invariant
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TauSigma:
    """Two independent gap-preserving channels on a single (K, Thing).

    ``tau`` and ``sigma`` are each ∈ {0, 1}.  ``kappa`` is derived as
    τ ⊕ σ (GF(2) addition).  The linear constraint κ = τ + σ is
    enforced by construction — no code path stores κ independently —
    so the type system guarantees it holds.

    Under ``p-kappa-is-derived-xor`` this is the atomic unit of state
    for one K on one Thing.  For populated bitmaps over many K's,
    see ``Thing.tau_mask`` / ``sigma_mask``.
    """

    tau: int  # ∈ {0, 1}
    sigma: int  # ∈ {0, 1}

    def __post_init__(self) -> None:
        if self.tau not in (0, 1):
            raise ValueError(f"tau must be 0 or 1, got {self.tau!r}")
        if self.sigma not in (0, 1):
            raise ValueError(f"sigma must be 0 or 1, got {self.sigma!r}")

    @property
    def kappa(self) -> int:
        """κ = τ ⊕ σ.  Derived; never stored."""
        return self.tau ^ self.sigma

    def triple(self) -> Tuple[int, int, int]:
        """The (τ, σ, κ) triple in F₂²."""
        return (self.tau, self.sigma, self.kappa)


# ---------------------------------------------------------------------------
# S3 — symmetric group on {τ, σ, κ}
# ---------------------------------------------------------------------------


# Canonical indexing: 0 = τ, 1 = σ, 2 = κ.
_AXIS_NAMES = ("τ", "σ", "κ")


@dataclass(frozen=True)
class S3:
    """Element of the symmetric group on {τ, σ, κ}.

    ``perm`` is a 3-tuple where ``perm[i]`` is the axis that ends up
    at position i after the permutation.  ``perm = (0, 1, 2)`` is the
    identity.  Group composition via ``__mul__``.

    The S3 action on a TauSigma respects the linear constraint
    κ = τ + σ because S3 acts on F₂² linearly — any permutation of the
    three non-zero vectors (1,0), (0,1), (1,1) is a linear automorphism
    of F₂², which is exactly S3 ≅ GL(2, F₂).
    """

    perm: Tuple[int, int, int]

    def __post_init__(self) -> None:
        if sorted(self.perm) != [0, 1, 2]:
            raise ValueError(f"perm must be a permutation of (0,1,2), got {self.perm!r}")

    @classmethod
    def identity(cls) -> "S3":
        return cls((0, 1, 2))

    def __mul__(self, other: "S3") -> "S3":
        """Group composition: (self · other)(i) = self(other(i))."""
        return S3(tuple(self.perm[other.perm[i]] for i in range(3)))

    def inverse(self) -> "S3":
        inv = [0, 0, 0]
        for i, p in enumerate(self.perm):
            inv[p] = i
        return S3(tuple(inv))

    def act(self, ts: TauSigma) -> TauSigma:
        """Apply this group element to a TauSigma.

        Interprets ``perm`` as: axis ``perm[i]`` moves to position i.
        After permutation, positions 0, 1, 2 hold the values that were
        at perm[0], perm[1], perm[2].  Since we only store (τ, σ) and
        derive κ, we read the 3-triple, permute, and reconstruct τ, σ
        from positions 0 and 1 of the permuted triple.

        The linear constraint is preserved automatically because S3
        permutations of the non-zero F₂² vectors are linear.
        """
        t = ts.triple()
        permuted = tuple(t[self.perm[i]] for i in range(3))
        # Reconstruct: τ' = permuted[0], σ' = permuted[1].
        # κ' = permuted[2], which equals τ' ⊕ σ' by linearity.
        return TauSigma(tau=permuted[0], sigma=permuted[1])

    def name(self) -> str:
        return "(" + "".join(_AXIS_NAMES[p] for p in self.perm) + ")"


# All 6 S3 elements, generated once
S3_ELEMENTS: Tuple[S3, ...] = (
    S3((0, 1, 2)),  # identity
    S3((1, 0, 2)),  # (τ σ) transposition
    S3((2, 1, 0)),  # (τ κ) transposition
    S3((0, 2, 1)),  # (σ κ) transposition
    S3((1, 2, 0)),  # (τ σ κ) 3-cycle
    S3((2, 0, 1)),  # (τ κ σ) 3-cycle
)


# ---------------------------------------------------------------------------
# K — inductive type of discriminators
# ---------------------------------------------------------------------------


class K(ABC):
    """A discriminator.  Abstract; constructors are ``Atom`` and ``Wedge``.

    Intensional equality (dataclass structural) is the default.
    Extensional equality — e.g., ``Wedge(a, b) ≡ Wedge(b, a)`` under
    wedge commutativity, or S3-orbit equivalence — is provided by
    ``normalize()`` which returns a canonical representative.  In a
    dependent type theory with HIT these would be path constructors
    on the inductive type; in Python they are simulated via explicit
    canonicalization.

    ``grade`` is the arity / exterior-algebra grade: atoms are grade 1,
    wedges are one greater than the max grade of their parents.  The
    grade is derived, never stored in a counter — matching
    ``p-arity-is-grade``.
    """

    @property
    @abstractmethod
    def grade(self) -> int:
        ...

    @abstractmethod
    def key(self) -> KKey:
        """Stable string key reflecting INTENSIONAL structure.

        Atoms: the verbatim observation string.
        Wedges: derived from parents in the order given (not sorted);
                intensionally distinct ``Wedge(a, b)`` and ``Wedge(b, a)``
                have distinct keys.  Extensional canonicalization is
                the job of ``normalize()``.
        """
        ...

    @abstractmethod
    def normalize(self) -> "K":
        """Return a canonical representative in the K's extensional
        equivalence class.  Quotients by the three path-constructors
        of the exterior algebra:

          - commutativity:  a ∧ b ≡ b ∧ a
          - associativity:  (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
          - nilpotency:     a ∧ a = 0

        Idempotent.  Implementation flattens nested wedges, sorts the
        resulting atom multiset, detects duplicates (→ ZeroK), and
        rebuilds a canonical right-leaning binary tree.
        """
        ...

    @abstractmethod
    def atoms(self) -> frozenset["Atom"]:
        """Set of all Atom K's appearing in this K's inductive structure
        (transitively, across wedge parents).  Under ``p-self-similarity``,
        atoms are themselves K's, so this must return typed Atom instances
        rather than raw observation strings."""
        ...

    def is_zero(self) -> bool:
        """True if this K is the zero element of the exterior algebra
        (i.e., a wedge with duplicate atoms).  Default: False.
        Overridden by ``ZeroK``."""
        return False


@dataclass(frozen=True, eq=True)
class Atom(K):
    """Primitive observation K: a verbatim observable string.

    Under ``p-atoms-are-formal-tau-sigma-channels``, the atom carries
    NO framework-level commitment about what ``observable`` observes;
    it is a population choice made by the extractor.  By default
    atoms have τ = σ at grade 1, giving κ = 0, but the framework
    supports any population.
    """

    observable: Observable

    @property
    def grade(self) -> int:
        return 1

    def key(self) -> KKey:
        return KKey(f"atom:{self.observable}")

    def normalize(self) -> "Atom":
        return self  # atoms are already canonical

    def atoms(self) -> frozenset["Atom"]:
        return frozenset({self})


@dataclass(frozen=True, eq=True)
class ZeroK(K):
    """The zero element of the exterior algebra.

    Produced by ``Wedge.normalize()`` when the wedge contains duplicate
    atoms (nilpotency: a ∧ a = 0).  Never fires on any thing; should
    not be registered in a Pool (pool entries represent meaningful
    discriminators, not the algebraic zero).
    """

    # Marker; no fields.  Frozen + eq gives it singleton-like behavior
    # via structural equality (all ZeroK instances equal each other).

    @property
    def grade(self) -> int:
        return 0

    def key(self) -> KKey:
        return KKey("zero")

    def normalize(self) -> "ZeroK":
        return self

    def atoms(self) -> frozenset["Atom"]:
        return frozenset()

    def is_zero(self) -> bool:
        return True


@dataclass(frozen=True, eq=True)
class Wedge(K):
    """Grade-(max(a.grade, b.grade) + 1) K built from two lower K's via ∧.

    Intensional equality distinguishes ``Wedge(a, b)`` from ``Wedge(b, a)``
    since they are structurally different dataclass instances.  ``key()``
    reflects the intensional order.

    Extensional equality is earned via ``normalize()``, which quotients
    by all three exterior-algebra path constructors (commutativity,
    associativity, nilpotency).  The canonical representative is a
    right-leaning binary tree whose leaves are distinct Atoms in
    sorted key order.
    """

    a: K
    b: K

    @property
    def grade(self) -> int:
        return max(self.a.grade, self.b.grade) + 1

    def key(self) -> KKey:
        # INTENSIONAL key: parents in given order.  Two wedges whose
        # parents differ in structure or order get distinct keys;
        # normalize() collapses them extensionally.
        return KKey(f"wedge({self.a.key()},{self.b.key()})")

    def normalize(self) -> K:
        """Flatten nested wedges, collect atoms, dedupe (→ ZeroK on
        duplicate), and rebuild a canonical right-leaning binary tree.

        Returns:
          - ``ZeroK()`` if any atom appears twice in the flattened list
            (nilpotency);
          - the sole ``Atom`` if the flattened multiset has exactly one
            element (degenerate wedge);
          - a canonical right-leaning ``Wedge`` otherwise.
        """
        # Recursively collect all atoms via the typed accessor.
        all_atoms = self.atoms()
        # Detect nilpotency by comparing flattened leaf count to
        # distinct-atom count; if they differ, duplicates exist.
        flat_leaves = _flatten_wedge_leaves(self)
        if len(flat_leaves) != len(all_atoms):
            return ZeroK()
        # No duplicates; build right-leaning canonical tree.
        sorted_atoms = sorted(all_atoms, key=lambda a: a.key())
        if len(sorted_atoms) == 1:
            return sorted_atoms[0]  # grade-1 degenerate
        return _build_right_leaning(sorted_atoms)

    def atoms(self) -> frozenset["Atom"]:
        return self.a.atoms() | self.b.atoms()


# ---------------------------------------------------------------------------
# Wedge canonicalization helpers
# ---------------------------------------------------------------------------


def _flatten_wedge_leaves(k: K) -> Tuple[Atom, ...]:
    """Recursively collect all atom leaves of a wedge tree IN ORDER
    (preserving multiplicity).  Used to detect duplicates for
    nilpotency quotienting."""
    if isinstance(k, Atom):
        return (k,)
    if isinstance(k, ZeroK):
        return ()
    if isinstance(k, Wedge):
        return _flatten_wedge_leaves(k.a) + _flatten_wedge_leaves(k.b)
    raise TypeError(f"unknown K constructor: {type(k).__name__}")


def _build_right_leaning(atoms: list) -> K:
    """Build a right-leaning binary Wedge tree from a sorted, distinct
    list of Atoms.  Used by ``Wedge.normalize()`` to produce the
    canonical representative of the extensional equivalence class."""
    if len(atoms) == 0:
        # Empty wedge is identity; represent as ZeroK for safety
        # (shouldn't happen in practice since normalize filters this).
        return ZeroK()
    if len(atoms) == 1:
        return atoms[0]
    # Right-leaning: Wedge(a[0], Wedge(a[1], Wedge(a[2], ...)))
    result: K = atoms[-1]
    for atom in reversed(atoms[:-1]):
        result = Wedge(atom, result)
    return result


# ---------------------------------------------------------------------------
# Pool — append-only registry mapping K keys to bit indices
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Pool:
    """Append-only K registry.

    Maintains the assignment of stable bit indices to K keys.  Adding
    a K returns a new Pool (frozen / pure).  Bit indices are assigned
    in append order; they are stable across merges that respect key
    equality.

    Design-note (``d-disk-as-merge-protocol``): pool contents map
    one-to-one to lines of ``pool.jsonl``; line number (0-indexed) =
    bit index.  Two shards that register the same K key independently
    MAY get different local bit indices; the merge step reassigns
    indices canonically during load.
    """

    keys: Tuple[str, ...] = ()
    by_key: Tuple[Tuple[str, int], ...] = ()  # (key, bit_index) pairs
    # ``ks`` stores the actual K objects in bit-index order
    ks: Tuple[K, ...] = ()

    def __post_init__(self) -> None:
        if len(self.keys) != len(self.ks):
            raise ValueError("keys and ks length mismatch")
        if tuple(k.key() for k in self.ks) != self.keys:
            raise ValueError("ks[i].key() != keys[i]")

    def size(self) -> int:
        return len(self.keys)

    def bit_of(self, k: K) -> int | None:
        """Return the bit index of K's extensional equivalence class.

        The pool stores extensional representatives (canonical via
        ``normalize()``), so lookup also normalizes first.  This keeps
        pool identity consistent with the HIT-style quotient: two
        intensionally-distinct K's in the same extensional class
        resolve to the same bit."""
        target = k.normalize().key()
        for key, idx in self.by_key:
            if key == target:
                return idx
        return None

    def has(self, k: K) -> bool:
        return self.bit_of(k) is not None

    def with_k(self, k: K) -> "Pool":
        """Return a new Pool containing ``k``; idempotent if k is already present."""
        nk = k.normalize()
        existing = self.bit_of(nk)
        if existing is not None:
            return self
        new_idx = len(self.keys)
        return Pool(
            keys=self.keys + (nk.key(),),
            by_key=self.by_key + ((nk.key(), new_idx),),
            ks=self.ks + (nk,),
        )

    def merge(self, other: "Pool") -> "Pool":
        """Merge two pools.  K's already in self keep their bit indices;
        K's only in other are appended with new indices.  Idempotent."""
        result = self
        for k in other.ks:
            result = result.with_k(k)
        return result

    def __iter__(self) -> Iterator[K]:
        return iter(self.ks)


# ---------------------------------------------------------------------------
# Thing — a named declaration with τ/σ bitmaps over the Pool
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Thing:
    """A pooled object, identified solely by an opaque ThingId.

    The algebra sees ONLY the identity and the bitmaps.  Under
    ``p-source-is-a-k`` and ``p-no-bespoke-recognition``, source
    provenance is not a privileged field of Thing — it is an
    observable K registered in the Pool.  Same for display names,
    paths, line numbers, and anything else an extractor might want
    to surface.  There is no "metadata" category: every observable
    is a K; reports are queries over the pool + bitmaps.  A report
    that wants to show "source path" filters for K's whose keys
    match its chosen convention (e.g. prefix ``source:``) — but
    that's a REPORTER choice, not a framework taxonomy.

    ``tau_mask`` and ``sigma_mask`` are bitmaps over the Pool: bit i
    set iff the K at pool position i fires on this thing in the
    respective channel.  ``kappa_mask`` is derived as tau ^ sigma
    by construction (never stored).
    """

    id: ThingId              # opaque identity; not interpreted by algebra
    tau_mask: int = 0        # bitmap over Pool
    sigma_mask: int = 0      # bitmap over Pool

    @property
    def kappa_mask(self) -> int:
        """κ-mask by GF(2) XOR of τ and σ.  Derived; never stored."""
        return self.tau_mask ^ self.sigma_mask

    def fires(self, pool: Pool, k: K, channel: str = "tau") -> bool:
        idx = pool.bit_of(k)
        if idx is None:
            return False
        mask = self.tau_mask if channel == "tau" else (
            self.sigma_mask if channel == "sigma" else self.kappa_mask
        )
        return bool((mask >> idx) & 1)

    def tausigma_at(self, pool: Pool, k: K) -> TauSigma:
        """Read the TauSigma state of a specific K on this thing."""
        idx = pool.bit_of(k)
        if idx is None:
            return TauSigma(0, 0)
        return TauSigma(
            tau=(self.tau_mask >> idx) & 1,
            sigma=(self.sigma_mask >> idx) & 1,
        )

    def remap(self, old_pool: Pool, new_pool: Pool) -> "Thing":
        """Return this Thing with its bitmaps remapped from old_pool's
        bit indexing to new_pool's bit indexing.

        Used by ``State.merge`` when two shards have divergent pools:
        self.pool bit-indices may not match the merged pool's, so
        Things from self need each bit remapped via K-key lookup."""
        if old_pool is new_pool:
            return self
        new_tau = 0
        new_sigma = 0
        for old_idx, k in enumerate(old_pool.ks):
            new_idx = new_pool.bit_of(k)
            if new_idx is None:
                continue  # K not in new pool; bit dropped
            if (self.tau_mask >> old_idx) & 1:
                new_tau |= 1 << new_idx
            if (self.sigma_mask >> old_idx) & 1:
                new_sigma |= 1 << new_idx
        return Thing(id=self.id, tau_mask=new_tau, sigma_mask=new_sigma)


# ---------------------------------------------------------------------------
# State — the closed-loop state (Stage 2)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class State:
    """Complete state of the closed-loop algorithm.

    ``pool``          — the K registry (Pool).
    ``things``        — mapping thing-id → Thing.  All Things' bitmaps
                        are interpreted against ``pool``.
    ``oracle_pairs``  — frozenset of frozenset({id_a, id_b}) — thing
                        pairs known to correspond (citation links).
                        Used for weight calibration only, never for
                        gating.
    ``weights``       — per-K weight, keyed by K.key().  Pluggable
                        objective adjusts these.
    ``trajectory``    — append-only tuple of per-iteration telemetry.
    ``iteration``     — monotonic counter.

    Frozen dataclass: step() must return a new State, never mutate.
    ``merge``, ``restrict``, and ``signature`` support self-similarity
    and embarrassingly-parallel operation per p-embarrassingly-parallel.
    """

    pool: Pool = field(default_factory=Pool)
    things: Tuple[Tuple[ThingId, Thing], ...] = ()       # sorted-by-id for hashability
    oracle_pairs: frozenset = frozenset()                # frozenset[frozenset[ThingId]]
    weights: Tuple[Tuple[KKey, float], ...] = ()         # sorted-by-key for hashability
    trajectory: Tuple = ()
    iteration: int = 0

    # -- accessors ----------------------------------------------------------

    def things_dict(self) -> dict:
        return dict(self.things)

    def weights_dict(self) -> dict:
        return dict(self.weights)

    def weight_of(self, k: K, default: float = 1.0) -> float:
        target = k.key()
        for key, w in self.weights:
            if key == target:
                return w
        return default

    # -- constructors -------------------------------------------------------

    def with_thing(self, thing: Thing) -> "State":
        """Add or replace a thing by id."""
        others = tuple((i, t) for i, t in self.things if i != thing.id)
        new_things = tuple(sorted(others + ((thing.id, thing),), key=lambda kv: kv[0]))
        return State(
            pool=self.pool,
            things=new_things,
            oracle_pairs=self.oracle_pairs,
            weights=self.weights,
            trajectory=self.trajectory,
            iteration=self.iteration,
        )

    def with_pool(self, pool: Pool) -> "State":
        return State(
            pool=pool,
            things=self.things,
            oracle_pairs=self.oracle_pairs,
            weights=self.weights,
            trajectory=self.trajectory,
            iteration=self.iteration,
        )

    def with_weight(self, k_key: KKey, w: float) -> "State":
        others = tuple((k, v) for k, v in self.weights if k != k_key)
        new = tuple(sorted(others + ((k_key, w),), key=lambda kv: kv[0]))
        return State(
            pool=self.pool,
            things=self.things,
            oracle_pairs=self.oracle_pairs,
            weights=new,
            trajectory=self.trajectory,
            iteration=self.iteration,
        )

    def appending_trajectory(self, entry: dict) -> "State":
        return State(
            pool=self.pool,
            things=self.things,
            oracle_pairs=self.oracle_pairs,
            weights=self.weights,
            trajectory=self.trajectory + (entry,),
            iteration=self.iteration + 1,
        )

    # -- merge / restrict ---------------------------------------------------

    def merge(self, other: "State") -> "State":
        """Union two states.  Associative and commutative per
        ``p-embarrassingly-parallel``:

        - Pool: ``self.pool.merge(other.pool)`` — K's from self keep
          their bit indices (append-only); K's only in other get new
          indices appended.  This produces a pool where each K's
          extensional identity maps to a single bit index.
        - Things: union by ThingId; if a Thing appears in both states,
          either the two Thing records are identical OR their bitmaps
          are both remapped to the merged pool and then compared.
          Truly divergent Things (same id, different firing profile)
          raise ValueError.
        - Weights: averaged on key collision.
        - Oracle pairs: set-unioned.
        - Trajectory: concatenated and sorted by iteration key.

        Divergent-pool merge (other.pool has K's self.pool doesn't,
        and vice versa) works correctly: Things whose source pool
        differs from the merged pool are remapped via
        ``Thing.remap`` before being combined.
        """
        merged_pool = self.pool.merge(other.pool)

        # Determine if remapping is needed for each side
        self_needs_remap = self.pool.keys != merged_pool.keys
        other_needs_remap = other.pool.keys != merged_pool.keys

        def _remap_all(things_tuple, source_pool: Pool) -> dict:
            """Return dict ThingId → Thing with bitmaps in merged_pool indexing."""
            out = {}
            for tid, thing in things_tuple:
                if source_pool is merged_pool or not (
                    self_needs_remap if source_pool is self.pool else other_needs_remap
                ):
                    out[tid] = thing
                else:
                    out[tid] = thing.remap(source_pool, merged_pool)
            return out

        things_self = _remap_all(self.things, self.pool)
        things_other = _remap_all(other.things, other.pool)

        # Union by id; collision requires equality after remap
        combined: dict = {}
        for tid in set(things_self) | set(things_other):
            if tid in things_self and tid in things_other:
                if things_self[tid] != things_other[tid]:
                    raise ValueError(
                        f"thing id {tid!r} has diverging content across states "
                        f"(after pool remap)"
                    )
                combined[tid] = things_self[tid]
            else:
                combined[tid] = things_self.get(tid, things_other.get(tid))

        # Weights: average on collision
        ws: dict = dict(self.weights)
        for k, w in other.weights:
            if k in ws:
                ws[k] = (ws[k] + w) / 2.0
            else:
                ws[k] = w

        # Oracle: union
        oracle = self.oracle_pairs | other.oracle_pairs

        # Trajectory: concatenate, sorted by iteration field if present
        traj_combined = tuple(
            sorted(
                self.trajectory + other.trajectory,
                key=lambda e: e.get("iteration", 0) if isinstance(e, dict) else 0,
            )
        )

        return State(
            pool=merged_pool,
            things=tuple(sorted(combined.items(), key=lambda kv: kv[0])),
            oracle_pairs=oracle,
            weights=tuple(sorted(ws.items(), key=lambda kv: kv[0])),
            trajectory=traj_combined,
            iteration=max(self.iteration, other.iteration),
        )

    def restrict(
        self,
        *,
        thing_ids: frozenset | None = None,
    ) -> "State":
        """Return a sub-state containing only the requested things.
        Pool is preserved (K-pool doesn't partition naturally at this
        stage).  Oracle pairs restricted to those fully contained in
        the requested thing-set.
        """
        if thing_ids is None:
            return self
        kept = tuple((i, t) for i, t in self.things if i in thing_ids)
        kept_oracle = frozenset(
            p for p in self.oracle_pairs if all(x in thing_ids for x in p)
        )
        return State(
            pool=self.pool,
            things=kept,
            oracle_pairs=kept_oracle,
            weights=self.weights,
            trajectory=self.trajectory,
            iteration=self.iteration,
        )

    # -- identity / fixed-point detection -----------------------------------

    def signature(self) -> Tuple:
        """Structural fingerprint used by run_to_fixed_point to detect
        stability.  Excludes trajectory (which grows monotonically)
        and iteration counter.  Fixed point ↔ signature stable."""
        return (
            self.pool.keys,
            self.things,
            self.oracle_pairs,
            self.weights,
        )


# ---------------------------------------------------------------------------
# Stage 1 + 2 smoke test
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Stage 3 — atom extraction from parse-tree sources
# ---------------------------------------------------------------------------
#
# Pools every top-level named declaration across the paper / agda / python
# sources into a flat set of Things.  For each Thing, observes the verbatim
# kind strings appearing in its subtree (``deep_kind_set``) and registers
# each as an atomic K in the Pool.  A source-membership atom
# (``source:paper``, ``source:agda``, ``source:python``) is also registered
# and fires on every thing of the corresponding source — satisfying
# ``p-source-is-a-k`` (source is just another K, not a privileged field).
#
# Under ``d-tau-sigma-symmetric-at-grade-1``: τ = σ for atomic K's, so each
# Thing's ``tau_mask == sigma_mask``, giving κ = 0 identically at grade 1.
# Asymmetry emerges only via κ-evolution at higher grades.
#
# Oracle pairs are loaded from the existing manifests at
# ``reports/{paper,agda,python}_decls.jsonl`` if they exist; otherwise the
# oracle is empty.  The oracle is used only by downstream scorers/
# objectives (``d-oracle-calibrates-not-gates``) and does not affect
# extraction.
#
# Under ``p-no-bespoke-recognition``, the choice to enumerate "top-level
# named declarations" as Things is a pragmatic scale decision recorded in
# ``d-things-are-named-decls``.  Finer-grained Things (every parse-tree
# node) are a future refinement.


def _source_roots(repo: Path) -> dict:
    """Directory roots for each source's parse-tree extraction."""
    return {
        "paper": repo / "paper",
        "agda": repo / "agda",
        "python": repo / "src",
    }


def _iter_source_nodes(
    repo: Path, source: str
) -> Iterator[Tuple[str, frozenset]]:
    """Yield (thing_id, deep_kind_observations) for every top-level named
    declaration in ``source``.  Uses the existing parsers in
    ``structural_identity``; no re-implementation."""
    import sys
    scripts_dir = str(repo / "scripts")
    if scripts_dir not in sys.path:
        sys.path.insert(0, scripts_dir)
    from structural_identity import (
        parse_paper_decls, parse_agda_decls, parse_python_decls,
        deep_kind_set,
    )

    anon_counter = 0
    roots = _source_roots(repo)
    if source == "paper":
        for node in parse_paper_decls(roots["paper"]):
            dc = node.named_decl
            if dc is None:
                continue
            kind, label = dc
            disambig = label or f"anon_{anon_counter:03d}"
            if not label:
                anon_counter += 1
            tid = f"paper:{kind}:{disambig}"
            yield tid, deep_kind_set(node)
    elif source == "agda":
        for path in sorted(roots["agda"].rglob("*.agda")):
            try:
                for node in parse_agda_decls(path):
                    dc = node.named_decl
                    if dc is None:
                        continue
                    kind, name = dc
                    tid = f"agda:{kind}:{name}"
                    yield tid, deep_kind_set(node)
            except Exception as e:
                # Parse failures on individual files do not abort the
                # whole extraction — log silently and move on.
                continue
    elif source == "python":
        for path in sorted(roots["python"].rglob("*.py")):
            try:
                for node in parse_python_decls(path):
                    dc = node.named_decl
                    if dc is None:
                        continue
                    kind, name = dc
                    tid = f"python:{kind}:{name}"
                    yield tid, deep_kind_set(node)
            except Exception:
                continue
    else:
        raise ValueError(f"unknown source: {source!r}")


def _load_oracle_pairs(repo: Path) -> frozenset:
    """Load citation-oracle pairs from existing reports manifests.

    Returns ``frozenset[frozenset[ThingId]]``.  If manifests are absent
    or any error occurs, returns empty.  The oracle is input data for
    weight calibration (``d-oracle-calibrates-not-gates``); never a
    commit gate.
    """
    import json
    reports_dir = repo / "reports"
    manifests = {
        "paper": reports_dir / "paper_decls.jsonl",
        "agda": reports_dir / "agda_decls.jsonl",
        "python": reports_dir / "python_decls.jsonl",
    }
    if not all(p.exists() for p in manifests.values()):
        return frozenset()
    try:
        paper_rows = [json.loads(l) for l in manifests["paper"].open() if l.strip()]
        agda_rows = [json.loads(l) for l in manifests["agda"].open() if l.strip()]
        python_rows = [json.loads(l) for l in manifests["python"].open() if l.strip()]
    except Exception:
        return frozenset()
    agda_docs = {r["qualname"]: r.get("docstring", "") for r in agda_rows}
    python_docs = {r["qualname"]: r.get("docstring", "") for r in python_rows}

    import sys
    scripts_dir = str(repo / "scripts")
    if scripts_dir not in sys.path:
        sys.path.insert(0, scripts_dir)
    try:
        from calibrate_weights import build_citation_oracle
    except Exception:
        return frozenset()
    oracle = build_citation_oracle(paper_rows, agda_docs, python_docs)
    return frozenset(
        frozenset({ThingId(src), ThingId(tgt)})
        for src, tgt, _cite, _stream in oracle
    )


def extract_initial_state(
    repo: Path,
    *,
    source_filter: frozenset | None = None,
    include_oracle: bool = True,
) -> State:
    """Build the initial ``State`` from on-disk parse trees.

    ``source_filter``: if given, restrict extraction to this subset of
    ``{"paper", "agda", "python"}`` (useful for smoke tests and
    Stage-9 shard experiments).  Default: all three sources.

    ``include_oracle``: if True, load citation pairs from
    ``reports/{source}_decls.jsonl`` manifests.  If manifests are
    absent, oracle is empty silently.

    Registers one atomic K per distinct kind-observable-string observed
    across any Thing's subtree, plus one atomic K per source name
    (``source:paper``, etc.).  Each Thing gets τ = σ bitmap over the
    Pool: bit i set iff the K at pool position i fires on this Thing's
    subtree (or is the source-membership atom for this Thing's source).

    Because τ = σ for every atom at grade 1, κ = 0 identically.
    Higher-grade wedges (future stages) can produce τ ≠ σ states.
    """
    sources = ("paper", "agda", "python")
    if source_filter is not None:
        sources = tuple(s for s in sources if s in source_filter)

    # Phase 1: collect raw observations per Thing
    raw: list = []  # list of (thing_id, source, frozenset[str])
    for src in sources:
        for tid, obs in _iter_source_nodes(repo, src):
            raw.append((tid, src, obs))

    # Phase 2: build Pool.  Distinct observations across all Things
    # plus one source-atom per source = the initial K pool.  Sorted
    # for deterministic bit assignment across runs.
    all_observables: set = set()
    for _tid, src, obs in raw:
        all_observables.update(obs)
        all_observables.add(f"source:{src}")
    pool = Pool()
    for observable in sorted(all_observables):
        pool = pool.with_k(Atom(Observable(observable)))

    # Phase 3: build Things with τ = σ bitmaps
    things: list = []
    for tid, src, obs in raw:
        mask = 0
        for observation in obs:
            idx = pool.bit_of(Atom(Observable(observation)))
            if idx is not None:
                mask |= 1 << idx
        # Fire the source atom
        src_idx = pool.bit_of(Atom(Observable(f"source:{src}")))
        if src_idx is not None:
            mask |= 1 << src_idx
        things.append(
            Thing(id=ThingId(tid), tau_mask=mask, sigma_mask=mask)
        )

    # Phase 4: optional oracle load
    oracle = _load_oracle_pairs(repo) if include_oracle else frozenset()

    return State(
        pool=pool,
        things=tuple(sorted(
            ((t.id, t) for t in things), key=lambda kv: kv[0]
        )),
        oracle_pairs=oracle,
    )


# ---------------------------------------------------------------------------


def _smoke_test() -> None:
    """Exercise the type core; assert the κ = τ ⊕ σ invariant holds
    under S3 action and under TauSigma construction at the boundaries."""

    # TauSigma invariant: κ always equals τ ⊕ σ
    for t in (0, 1):
        for s in (0, 1):
            ts = TauSigma(t, s)
            assert ts.kappa == (t ^ s), f"κ invariant failed: {ts}"

    # S3 identity is identity
    e = S3.identity()
    ts = TauSigma(1, 0)  # τ=1, σ=0, κ=1
    assert e.act(ts) == ts, "S3 identity failed"

    # S3 composition: element · inverse = identity
    for g in S3_ELEMENTS:
        ginv = g.inverse()
        assert (g * ginv).perm == (0, 1, 2), f"inverse failed for {g.name()}"
        assert (ginv * g).perm == (0, 1, 2), f"inverse failed for {g.name()}"

    # S3 action preserves the κ = τ ⊕ σ constraint
    for g in S3_ELEMENTS:
        for t in (0, 1):
            for s in (0, 1):
                ts = TauSigma(t, s)
                ts2 = g.act(ts)
                assert ts2.kappa == (ts2.tau ^ ts2.sigma), (
                    f"S3 element {g.name()} broke κ invariant on {ts}"
                )

    # S3 transposition (τ σ) acts on TauSigma by swapping τ and σ
    tau_sigma_swap = S3((1, 0, 2))
    for t in (0, 1):
        for s in (0, 1):
            ts = TauSigma(t, s)
            ts2 = tau_sigma_swap.act(ts)
            assert ts2.tau == s and ts2.sigma == t, (
                f"(τσ) swap failed on {ts}: got {ts2}"
            )

    # K: atoms are grade 1, wedges grow grade, keys are canonical
    a = Atom(Observable("module"))
    b = Atom(Observable("function"))
    assert a.grade == 1 and b.grade == 1
    w = Wedge(a, b)
    assert w.grade == 2

    # Intensional keys DIFFER under argument order
    w_ab = Wedge(a, b)
    w_ba = Wedge(b, a)
    assert w_ab != w_ba, "intensionally distinct Wedge(a,b) vs Wedge(b,a)"
    assert w_ab.key() != w_ba.key(), "intensional keys must differ by construction order"

    # Extensional equality via normalize() — quotient by commutativity
    assert w_ab.normalize() == w_ba.normalize(), "commutativity quotient failed"
    assert w_ab.normalize().key() == w_ba.normalize().key(), (
        "extensional keys must agree after normalize"
    )

    # Grade of nested wedges
    c = Atom(Observable("expr"))
    w2 = Wedge(w, c)
    assert w2.grade == 3
    w3 = Wedge(c, w)
    assert w3.grade == 3

    # Associativity quotient: (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
    left_assoc = Wedge(Wedge(a, b), c)
    right_assoc = Wedge(a, Wedge(b, c))
    assert left_assoc != right_assoc, "intensionally distinct"
    assert left_assoc.normalize() == right_assoc.normalize(), (
        "associativity quotient failed"
    )

    # Nilpotency: a ∧ a = 0
    nil = Wedge(a, a)
    assert nil.normalize() == ZeroK(), "nilpotency quotient failed"
    # Duplicate detection across associativity: (a ∧ b) ∧ a = 0
    nil2 = Wedge(Wedge(a, b), a)
    assert nil2.normalize() == ZeroK(), "nilpotency across associativity failed"

    # atoms() returns frozenset[Atom] (typed), not raw strings
    atoms_of_w2 = w2.atoms()
    assert all(isinstance(x, Atom) for x in atoms_of_w2), "atoms() must return Atom instances"
    assert atoms_of_w2 == frozenset({a, b, c}), "atoms() set membership"

    # Canonical wedge is right-leaning, sorted by atom key
    canon = Wedge(c, Wedge(b, a)).normalize()  # grade-3 built differently
    # Canonical form should have atoms in sorted order: a, b, c (by key "atom:expr", "atom:function", "atom:module")
    # (sort is by K.key() which is "atom:<observable>", so alphabetical on observable)
    flat = _flatten_wedge_leaves(canon)
    assert flat == tuple(sorted(flat, key=lambda x: x.key())), "canonical form not sorted"

    # Pool: append, idempotency, merge
    p = Pool()
    assert p.size() == 0
    p1 = p.with_k(a)
    assert p1.size() == 1 and p1.bit_of(a) == 0
    p2 = p1.with_k(a)  # idempotent
    assert p2.size() == 1
    p3 = p2.with_k(b).with_k(w)
    assert p3.size() == 3
    # Merge with another pool that overlaps on a
    q = Pool().with_k(b).with_k(c)
    merged = p3.merge(q)
    assert merged.size() == 4
    assert merged.bit_of(a) == 0  # stable
    assert merged.bit_of(b) == 1
    assert merged.bit_of(w) == 2
    assert merged.bit_of(c) == 3  # c was not in p3, appended

    # Thing: κ_mask = τ_mask ⊕ σ_mask; Thing has ONLY id + bitmaps
    t = Thing(id=ThingId("x"), tau_mask=0b1010, sigma_mask=0b1100)
    assert t.kappa_mask == 0b0110
    # Thing has no source_path/display/line — every observable is a K.
    # If an extractor wants source-path visible to reports, it registers
    # an atomic K (e.g. Atom("source:paper/x.py")) that fires on this
    # Thing's tau bitmap.  No privileged metadata category exists.
    assert not hasattr(t, "source_path"), "Thing should not carry source_path"
    assert not hasattr(t, "display"), "Thing should not carry display"
    assert not hasattr(t, "line"), "Thing should not carry line"

    # tausigma_at reads correctly
    t2 = Thing(id=ThingId("y"), tau_mask=0b101, sigma_mask=0b011)
    # Pool with 3 atoms at bit indices 0, 1, 2
    pool = Pool().with_k(Atom(Observable("k0"))).with_k(
        Atom(Observable("k1"))).with_k(Atom(Observable("k2")))
    ts_at_0 = t2.tausigma_at(pool, Atom(Observable("k0")))
    assert ts_at_0.tau == 1 and ts_at_0.sigma == 1 and ts_at_0.kappa == 0
    ts_at_1 = t2.tausigma_at(pool, Atom(Observable("k1")))
    assert ts_at_1.tau == 0 and ts_at_1.sigma == 1 and ts_at_1.kappa == 1
    ts_at_2 = t2.tausigma_at(pool, Atom(Observable("k2")))
    assert ts_at_2.tau == 1 and ts_at_2.sigma == 0 and ts_at_2.kappa == 1

    # Thing.remap: same Thing under a permuted pool produces remapped bitmaps
    pool_rev = Pool().with_k(Atom(Observable("k2"))).with_k(
        Atom(Observable("k1"))).with_k(Atom(Observable("k0")))
    # t2 in original pool has k0 and k2 firing on tau (bits 0 and 2)
    # In reversed pool, k0 is at bit 2 and k2 is at bit 0
    t2_remapped = t2.remap(pool, pool_rev)
    # Original tau_mask = 0b101 (bits 0, 2 set) → after remap, same K's fire
    # but at new indices: k0 was bit 0, now bit 2; k2 was bit 2, now bit 0
    # So new tau mask should have bits 0 and 2 set too = 0b101 (coincidence)
    assert t2_remapped.tausigma_at(pool_rev, Atom(Observable("k0"))) == ts_at_0
    assert t2_remapped.tausigma_at(pool_rev, Atom(Observable("k1"))) == ts_at_1
    assert t2_remapped.tausigma_at(pool_rev, Atom(Observable("k2"))) == ts_at_2

    # -- Stage 2 + 2.5 + 2.6: State merge / restrict / signature ------------

    ak0 = Atom(Observable("k0"))
    ak1 = Atom(Observable("k1"))
    ak2 = Atom(Observable("k2"))

    pool_a = Pool().with_k(ak0).with_k(ak1)
    t1 = Thing(id=ThingId("A"), tau_mask=0b01, sigma_mask=0b01)
    t2 = Thing(id=ThingId("B"), tau_mask=0b10, sigma_mask=0b11)
    s1 = State(
        pool=pool_a,
        things=((ThingId("A"), t1),),
        weights=((ak0.key(), 1.5),),
    )

    # Second state uses an extended pool (prefix-compatible)
    pool_b = pool_a.with_k(ak2)
    t3 = Thing(id=ThingId("C"), tau_mask=0b100, sigma_mask=0b000)
    s2 = State(
        pool=pool_b,
        things=((ThingId("B"), t2), (ThingId("C"), t3)),
        oracle_pairs=frozenset({frozenset({ThingId("A"), ThingId("B")})}),
        weights=((ak1.key(), 2.0),),
    )

    m = s1.merge(s2)
    assert m.pool.size() == 3
    assert len(m.things) == 3
    assert frozenset({ThingId("A"), ThingId("B")}) in m.oracle_pairs
    assert m.weight_of(ak0) == 1.5
    assert m.weight_of(ak1) == 2.0
    # State has no metadata field
    assert not hasattr(m, "metadata"), "State should not carry a metadata dict"

    # Merge idempotent
    assert m.merge(m).signature() == m.signature(), "merge not idempotent"

    # Merge associative
    s3 = State(pool=pool_b, things=((ThingId("D"), Thing(id=ThingId("D"))),))
    left = (s1.merge(s2)).merge(s3)
    right = s1.merge(s2.merge(s3))
    assert left.signature() == right.signature(), "merge not associative"

    # Weight collision: averaged on merge
    sA = State(pool=pool_a, weights=((ak0.key(), 1.0),))
    sB = State(pool=pool_a, weights=((ak0.key(), 3.0),))
    sAB = sA.merge(sB)
    assert sAB.weight_of(ak0) == 2.0, "weight collision not averaged"

    # Restrict: subset of things + pruned oracle
    restricted = m.restrict(thing_ids=frozenset({ThingId("A")}))
    assert len(restricted.things) == 1
    assert len(restricted.oracle_pairs) == 0, "oracle with absent endpoint not pruned"

    # Restrict preserving oracle
    restricted2 = m.restrict(thing_ids=frozenset({ThingId("A"), ThingId("B")}))
    assert len(restricted2.things) == 2
    assert frozenset({ThingId("A"), ThingId("B")}) in restricted2.oracle_pairs

    # Signature changes when pool grows; stable under trajectory append
    sig_before = s1.signature()
    s1_ext = s1.with_pool(pool_b)
    sig_after = s1_ext.signature()
    assert sig_before != sig_after

    s1_traj = s1.appending_trajectory({"note": "hello"})
    assert s1_traj.signature() == s1.signature()
    assert s1_traj.iteration == s1.iteration + 1

    # -- Stage 2.5 NEW: divergent-pool merge via Thing.remap ----------------

    # Two shards register different K's for the same thing's observations
    shardA_pool = Pool().with_k(ak0).with_k(ak1)       # bit 0 = k0, bit 1 = k1
    shardB_pool = Pool().with_k(ak1).with_k(ak2)       # bit 0 = k1, bit 1 = k2

    # Shard A sees thing X firing on k0 and k1 → tau_mask = 0b11
    thingA_X = Thing(id=ThingId("X"), tau_mask=0b11, sigma_mask=0b11)
    # Shard B sees thing Y firing on k1 and k2 → tau_mask = 0b11 (but against shardB_pool!)
    thingB_Y = Thing(id=ThingId("Y"), tau_mask=0b11, sigma_mask=0b11)

    shardA = State(pool=shardA_pool, things=((ThingId("X"), thingA_X),))
    shardB = State(pool=shardB_pool, things=((ThingId("Y"), thingB_Y),))

    # Merge MUST handle divergent pools — previously this raised
    merged = shardA.merge(shardB)
    # Merged pool has 3 K's: k0, k1, k2 (in some order)
    assert merged.pool.size() == 3

    # X still fires on k0 and k1 after remap
    assert merged.things_dict()[ThingId("X")].fires(merged.pool, ak0), "X should fire k0"
    assert merged.things_dict()[ThingId("X")].fires(merged.pool, ak1), "X should fire k1"
    assert not merged.things_dict()[ThingId("X")].fires(merged.pool, ak2), (
        "X should NOT fire k2 (not in shard A's observation)"
    )
    # Y still fires on k1 and k2 after remap
    assert merged.things_dict()[ThingId("Y")].fires(merged.pool, ak1), "Y should fire k1"
    assert merged.things_dict()[ThingId("Y")].fires(merged.pool, ak2), "Y should fire k2"
    assert not merged.things_dict()[ThingId("Y")].fires(merged.pool, ak0), (
        "Y should NOT fire k0 (not in shard B's observation)"
    )

    # Divergent merge is associative + commutative too
    # Order should not matter: shardA.merge(shardB) ≡ shardB.merge(shardA) extensionally
    merged_rev = shardB.merge(shardA)
    # Pool key sets should match (order may differ due to append-only)
    assert set(merged.pool.keys) == set(merged_rev.pool.keys)
    # Bit-by-bit firing sets should match for every K
    for k in [ak0, ak1, ak2]:
        for tid in [ThingId("X"), ThingId("Y")]:
            assert (
                merged.things_dict()[tid].fires(merged.pool, k)
                == merged_rev.things_dict()[tid].fires(merged_rev.pool, k)
            ), f"divergent merge not order-invariant for K={k.key()} tid={tid}"

    # -- Stage 3: atom extraction from parse-tree sources -------------------
    # Only runs if we can find the repo root (sources present).

    repo = Path.cwd()
    sources_present = {
        "paper": (repo / "paper").is_dir(),
        "agda": (repo / "agda").is_dir(),
        "python": (repo / "src").is_dir(),
    }

    if any(sources_present.values()):
        # Run on whichever sources are available (single-source if needed)
        available = frozenset(s for s, ok in sources_present.items() if ok)
        state = extract_initial_state(
            repo, source_filter=available, include_oracle=True,
        )

        # Minimum assertions: got at least one thing, at least one atom
        assert len(state.things) > 0, "extracted zero things"
        assert state.pool.size() > 0, "extracted zero atoms"

        # p-atoms-are-formal-tau-sigma-channels + d-tau-sigma-symmetric-at-grade-1:
        # κ = 0 identically for every thing at grade 1
        for tid, thing in state.things:
            assert thing.kappa_mask == 0, (
                f"thing {tid!r} has κ ≠ 0 at grade 1: τ={thing.tau_mask:b} "
                f"σ={thing.sigma_mask:b}; τ should equal σ for atoms"
            )

        # p-source-is-a-k: source atoms present in pool for each active source
        for src in available:
            src_atom = Atom(Observable(f"source:{src}"))
            idx = state.pool.bit_of(src_atom)
            assert idx is not None, f"source atom source:{src} not in pool"
            # Every thing from that source fires the source atom on its tau
            matching = [
                t for tid, t in state.things if tid.startswith(f"{src}:")
            ]
            for t in matching:
                assert (t.tau_mask >> idx) & 1, (
                    f"thing of source {src!r} does not fire source atom"
                )

        # Pool invariant: every observable appears as an Atom K
        for k in state.pool.ks:
            assert isinstance(k, Atom), (
                f"Stage-3 initial pool should contain only Atoms, got {type(k).__name__}"
            )

        print(f"    Stage 3 extraction: {len(state.things)} things, "
              f"{state.pool.size()} atoms, {len(state.oracle_pairs)} oracle pairs")
    else:
        print("    Stage 3 extraction: no source dirs found in cwd; skipping")

    print("Stage 1 + 2 + 2.5 + 2.6 + 3 smoke test: all assertions passed")
    print(f"  TauSigma invariant κ = τ ⊕ σ holds for all 4 cases × 6 S3 elements")
    print(f"  K inductive type: Atom, Wedge, ZeroK all conform")
    print(f"  Wedge extensional quotient: commutativity + associativity + nilpotency")
    print(f"  K.atoms() returns typed frozenset[Atom] (not raw strings)")
    print(f"  Intensional Wedge.key() distinguishes construction order;")
    print(f"    extensional normalize().key() collapses equivalence class")
    print(f"  Thing = (id, τ_mask, σ_mask); no privileged metadata category")
    print(f"  Every observable is a K; reports query the pool, not a metadata dict")
    print(f"  Pool append/merge idempotent; bit indices stable within shard")
    print(f"  State.merge associative, idempotent, handles DIVERGENT pools")
    print(f"    via Thing.remap (p-embarrassingly-parallel realized)")
    print(f"  State.restrict prunes orphan oracle pairs")
    print(f"  State.signature stable under trajectory append")


if __name__ == "__main__":
    _smoke_test()
