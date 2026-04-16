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

import json
import sys
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
    def structure(self) -> tuple:
        """Bijective structured representation of this K.

        The structure IS the intensional identity of the K, encoded as
        a nested tuple whose first element is a type tag:
          - ``("atom", observable)``
          - ``("wedge", a.structure(), b.structure())``
          - ``("zero",)``

        Two K instances have equal structure iff they are intensionally
        identical.  ``structure`` is the canonical basis for ``key()``
        (derived via JSON serialization, which is round-trippable so
        bijectivity holds for any observable string content, including
        those containing commas, parentheses, or other would-be
        separators).  Under ``p-bijective-hash-consing``, this is the
        framework's commitment to injective key encoding.
        """
        ...

    def key(self) -> KKey:
        """Bijective string key reflecting INTENSIONAL structure.

        Derived from ``structure()`` via ``json.dumps``; decoded via
        ``json.loads``.  The round-trip identity holds for any
        observable content — escape-safety comes from JSON's string
        quoting, not from hand-chosen separator characters.

        Extensional canonicalization (wedge commutativity, associativity,
        nilpotency) is the job of ``normalize()``, not ``key()``.
        Intensionally distinct ``Wedge(a, b)`` and ``Wedge(b, a)`` have
        distinct keys; their ``normalize().key()`` agree.
        """
        return KKey(json.dumps(self.structure()))

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

    def structure(self) -> tuple:
        return ("atom", self.observable)

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

    def structure(self) -> tuple:
        return ("zero",)

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

    def structure(self) -> tuple:
        # INTENSIONAL structure: parents in given order.  JSON-encoding
        # guarantees bijectivity — commas/parens inside observable
        # strings cannot create ambiguity at this level.  normalize()
        # produces the canonical (sorted) structure for extensional
        # comparison.
        return ("wedge", self.a.structure(), self.b.structure())

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


def _tuples_eq_lists(a, b) -> bool:
    """Compare a tuple (possibly nested) against a list (possibly nested)
    for element-wise equality, accepting the tuple/list type asymmetry
    that comes from ``json.loads`` returning lists where the originals
    were tuples.  Used only in Stage-3.5 bijectivity smoke tests."""
    if isinstance(a, (tuple, list)) and isinstance(b, (tuple, list)):
        if len(a) != len(b):
            return False
        return all(_tuples_eq_lists(x, y) for x, y in zip(a, b))
    return a == b


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


def _make_thing_id(source: str, kind: str, name: str | None,
                   source_path: str, source_line: int,
                   in_file_seq: int) -> str:
    """Build a bijective ThingId.

    Paper (LaTeX labels are globally unique within a document):
      labeled:   ``paper:{kind}:{label}``
      unlabeled: ``paper:{kind}:@{source_path}#n{in_file_seq}``

    Agda / Python (identifiers collide across modules/classes, so
    path is required for uniqueness):
      always: ``{source}:{kind}:@{source_path}#{name_or_seq}``

    Both branches are bijective:
      - Paper labels are LaTeX-enforced unique (\\label{} must be
        distinct); unlabeled decls get path+seq disambiguation.
      - Agda/Python names are unique within a file's scope; path
        is the globally-unique disambiguator.

    Stability: parser traversal is deterministic; in_file_seq comes
    from a per-file counter, never global; results are shard-stable.

    Under ``p-bijective-hash-consing`` the asymmetry between paper
    and code sources is accepted because the uniqueness guarantees
    differ (paper is corpus-globally unique by label; code is
    per-file-unique by identifier).  Both schemes remain injective.
    """
    if source == "paper":
        if name:
            return f"paper:{kind}:{name}"
        return f"paper:{kind}:@{source_path}#n{in_file_seq}"
    name_part = name if name else f"n{in_file_seq}"
    return f"{source}:{kind}:@{source_path}#{name_part}"


def _iter_source_nodes(
    repo: Path, source: str
) -> Iterator[Tuple[str, frozenset, dict]]:
    """Yield (thing_id, subtree_kind_observations, identity_components)
    for every top-level named declaration in ``source``.

    ``identity_components`` is a dict with keys:
      - ``"kind_at_root"``: the decl's own top-level kind string
      - ``"path_components"``: frozenset of path fragments (directory
        components + filename) from the source path
      - ``"name_verbatim"``: the decl's verbatim label/name if any,
        else None
      - ``"source"``: the source tag string ("paper", "agda", "python")

    Under ``p-yoneda-identity`` these components must be surfaced as
    probes so the identity is expressible by probe quotienting, not
    just by parsing opaque ThingId strings.  See ``extract_initial_state``
    for how they're registered as atomic K's.

    Parse failures are logged to stderr rather than silently swallowed.
    """
    scripts_dir = str(repo / "scripts")
    if scripts_dir not in sys.path:
        sys.path.insert(0, scripts_dir)
    from structural_identity import (
        parse_paper_decls, parse_agda_decls, parse_python_decls,
        deep_kind_set,
    )

    roots = _source_roots(repo)
    anon_seq: dict = {}

    def _next_anon(path_str: str) -> int:
        i = anon_seq.get(path_str, 0)
        anon_seq[path_str] = i + 1
        return i

    def _rel(p) -> str:
        s = str(p)
        if not s:
            return s
        pp = Path(s)
        if pp.is_absolute():
            try:
                pp = pp.relative_to(repo)
            except ValueError:
                pass
        return str(pp)

    def _path_components(path_str: str) -> frozenset:
        """Split a path into its directory/file components.  Each
        component becomes a half-space probe."""
        if not path_str:
            return frozenset()
        return frozenset(p for p in Path(path_str).parts if p)

    def _identity(kind: str, name, path_str: str) -> dict:
        return {
            "source": source,
            "kind_at_root": kind,
            "path_components": _path_components(path_str),
            "name_verbatim": name if name else None,
        }

    if source == "paper":
        for node in parse_paper_decls(roots["paper"]):
            dc = node.named_decl
            if dc is None:
                continue
            kind, label = dc
            path_str = _rel(getattr(node, "source_path", ""))
            in_file_seq = 0 if label else _next_anon(path_str)
            tid = _make_thing_id(
                source="paper", kind=kind, name=label,
                source_path=path_str,
                source_line=getattr(node, "source_line", 0),
                in_file_seq=in_file_seq,
            )
            yield tid, deep_kind_set(node), _identity(kind, label, path_str)
    elif source == "agda":
        for path in sorted(roots["agda"].rglob("*.agda")):
            rel_path = _rel(path)
            try:
                for node in parse_agda_decls(path):
                    dc = node.named_decl
                    if dc is None:
                        continue
                    kind, name = dc
                    in_file_seq = 0 if name else _next_anon(rel_path)
                    tid = _make_thing_id(
                        source="agda", kind=kind, name=name,
                        source_path=rel_path,
                        source_line=getattr(node, "source_line", 0),
                        in_file_seq=in_file_seq,
                    )
                    yield tid, deep_kind_set(node), _identity(kind, name, rel_path)
            except Exception as e:
                print(
                    f"closed_loop: parse failure in {path}: "
                    f"{type(e).__name__}: {e}",
                    file=sys.stderr,
                )
                continue
    elif source == "python":
        for path in sorted(roots["python"].rglob("*.py")):
            rel_path = _rel(path)
            try:
                for node in parse_python_decls(path):
                    dc = node.named_decl
                    if dc is None:
                        continue
                    kind, name = dc
                    in_file_seq = 0 if name else _next_anon(rel_path)
                    tid = _make_thing_id(
                        source="python", kind=kind, name=name,
                        source_path=rel_path,
                        source_line=getattr(node, "source_line", 0),
                        in_file_seq=in_file_seq,
                    )
                    yield tid, deep_kind_set(node), _identity(kind, name, rel_path)
            except Exception as e:
                print(
                    f"closed_loop: parse failure in {path}: "
                    f"{type(e).__name__}: {e}",
                    file=sys.stderr,
                )
                continue
    else:
        raise ValueError(f"unknown source: {source!r}")


def _qn_candidate_ids(row: dict) -> list:
    """Generate candidate closed_loop ThingIds for a manifest row.

    Returns multiple candidates because the old-pipeline manifests
    use slightly different naming conventions than the closed_loop
    extractor — in particular, agda module records store the short
    name (``All``) while the closed_loop extractor uses the full
    dotted name (``CSTZ.All``) derived from tree-sitter-agda.  The
    loader tries each candidate and keeps whichever is present in
    the actual extracted things dict.

    Under ``p-bijective-hash-consing``, the closed_loop format
    itself is bijective; the candidates here are only compensation
    for the naming-convention mismatch at the interface boundary
    between two systems, not an ambiguity in the ID format.
    """
    source = row.get("source")
    kind = row.get("kind")
    name = row.get("name") or row.get("label") or ""
    qualname = row.get("qualname") or ""
    path = row.get("path") or ""
    if not (source and kind and path):
        return []

    candidates: list = []
    label = row.get("label")
    if source == "paper":
        # Paper uses label-only IDs (LaTeX labels are corpus-globally
        # unique).  ``name`` is the paper decl's human-readable title
        # which doesn't match the extractor's ID convention.
        if label:
            candidates.append(f"paper:{kind}:{label}")
        if name and name != label:
            candidates.append(f"paper:{kind}:{name}")
    else:
        # agda/python: path-prefixed IDs.
        if name:
            candidates.append(f"{source}:{kind}:@{path}#{name}")
        if qualname and qualname != name:
            candidates.append(f"{source}:{kind}:@{path}#{qualname}")
        if label and label != name and label != qualname:
            candidates.append(f"{source}:{kind}:@{path}#{label}")
    return candidates


def _load_oracle_pairs(repo: Path, extracted_ids: set | None = None) -> frozenset:
    """Load citation-oracle pairs from existing reports manifests.

    Returns ``frozenset[frozenset[ThingId]]``.  If manifests are absent
    or any error occurs, returns empty.  The oracle is input data for
    weight calibration (``d-oracle-calibrates-not-gates``); never a
    commit gate.

    ``extracted_ids``: if provided, remap candidates are filtered to
    those actually present in the extracted state.  This handles
    naming-convention drift between the old pipeline's manifest
    format and the closed_loop's extraction format.
    """
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

    # Build lookup-qualname → new-ThingId remap.  The lookup qualname
    # is what build_citation_oracle emits, which for paper rows is
    # ``f"paper:{kind}:{label}"`` and for agda/python is the manifest
    # ``qualname`` field unchanged.
    remap: dict = {}
    for r in paper_rows:
        lookup_qn = f"paper:{r.get('kind')}:{r.get('label')}" if r.get('label') else None
        if not lookup_qn:
            continue
        for cand in _qn_candidate_ids(r):
            if extracted_ids is None or cand in extracted_ids:
                remap[lookup_qn] = cand
                break
    for r in agda_rows + python_rows:
        qn = r.get("qualname")
        if not qn:
            continue
        for cand in _qn_candidate_ids(r):
            if extracted_ids is None or cand in extracted_ids:
                remap[qn] = cand
                break

    agda_docs = {r["qualname"]: r.get("docstring", "") for r in agda_rows}
    python_docs = {r["qualname"]: r.get("docstring", "") for r in python_rows}

    scripts_dir = str(repo / "scripts")
    if scripts_dir not in sys.path:
        sys.path.insert(0, scripts_dir)
    try:
        from calibrate_weights import build_citation_oracle
    except Exception:
        return frozenset()
    oracle = build_citation_oracle(paper_rows, agda_docs, python_docs)

    pairs = set()
    for src, tgt, _cite, _stream in oracle:
        src_new = remap.get(src)
        tgt_new = remap.get(tgt)
        if src_new is None or tgt_new is None:
            continue
        pairs.add(frozenset({ThingId(src_new), ThingId(tgt_new)}))
    return frozenset(pairs)


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

    # Phase 1: collect raw observations + identity components per Thing
    raw: list = []  # list of (thing_id, source, frozenset[str], identity_dict)
    seen_ids: set = set()
    for src in sources:
        for tid, obs, identity in _iter_source_nodes(repo, src):
            if tid in seen_ids:
                raise ValueError(
                    f"thing-id collision: {tid!r} extracted twice "
                    f"(violates p-bijective-hash-consing; upgrade to "
                    f"byte-level positional disambiguation)"
                )
            seen_ids.add(tid)
            raw.append((tid, src, obs, identity))

    # Phase 2: build Pool.  Register probes for every discriminable
    # identity component so probe-quotienting can resolve any subset
    # expressible as a constraint on identity (p-yoneda-identity,
    # p-probes-are-half-spaces).
    all_observables: set = set()
    for _tid, src, obs, identity in raw:
        # Subtree kind observations (existing)
        all_observables.update(obs)
        # Source tag as probe (p-source-is-a-k)
        all_observables.add(f"source:{src}")
        # Top-level kind: distinct probe from subtree-kind.  Fires on
        # things whose own kind at the root is K (vs containing K
        # anywhere in subtree).  This distinction is discriminable
        # and therefore must be a probe per p-yoneda-identity.
        all_observables.add(f"kind_at_root:{identity['kind_at_root']}")
        # Path components: one probe per directory/file fragment.
        # Enables "things in this directory" as a probe quotient.
        for pc in identity["path_components"]:
            all_observables.add(f"path:{pc}")
        # Name verbatim (no tokenization — tokenizing would be
        # canonicalization, forbidden by p-no-canonicalization).
        # Same-named things across files share this probe; different
        # names are distinct probes.
        if identity["name_verbatim"]:
            all_observables.add(f"name:{identity['name_verbatim']}")
    pool = Pool()
    for observable in sorted(all_observables):
        pool = pool.with_k(Atom(Observable(observable)))

    # Phase 3: build Things with τ = σ bitmaps, firing all relevant
    # probes for each Thing's identity components.
    things: list = []
    for tid, src, obs, identity in raw:
        mask = 0
        # Subtree kind observations
        for observation in obs:
            idx = pool.bit_of(Atom(Observable(observation)))
            if idx is not None:
                mask |= 1 << idx
        # Source atom
        src_idx = pool.bit_of(Atom(Observable(f"source:{src}")))
        if src_idx is not None:
            mask |= 1 << src_idx
        # kind_at_root atom
        kroot_idx = pool.bit_of(
            Atom(Observable(f"kind_at_root:{identity['kind_at_root']}"))
        )
        if kroot_idx is not None:
            mask |= 1 << kroot_idx
        # path: component atoms
        for pc in identity["path_components"]:
            p_idx = pool.bit_of(Atom(Observable(f"path:{pc}")))
            if p_idx is not None:
                mask |= 1 << p_idx
        # name:verbatim atom (if named)
        if identity["name_verbatim"]:
            n_idx = pool.bit_of(
                Atom(Observable(f"name:{identity['name_verbatim']}"))
            )
            if n_idx is not None:
                mask |= 1 << n_idx
        things.append(
            Thing(id=ThingId(tid), tau_mask=mask, sigma_mask=mask)
        )

    # Phase 4: optional oracle load (remap uses extracted IDs to
    # resolve naming-convention drift between old and new formats)
    if include_oracle:
        extracted_ids = {t.id for t in things}
        oracle = _load_oracle_pairs(repo, extracted_ids=extracted_ids)
    else:
        oracle = frozenset()

    return State(
        pool=pool,
        things=tuple(sorted(
            ((t.id, t) for t in things), key=lambda kv: kv[0]
        )),
        oracle_pairs=oracle,
    )


# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Stage 4 — Scorer and Objective protocols
# ---------------------------------------------------------------------------
#
# Two pluggable-function types govern κ-evolution:
#
#   Scorer    (State, K, K) → float      — evaluates a candidate wedge
#                                           K_i ∧ K_j; higher = more useful
#   Objective (State) → float            — evaluates the current state;
#                                           weights tune to maximize this
#
# Framework commits to the PROTOCOLS, not to specific picks
# (d-articulation-scorer-pluggable, d-weight-objective-pluggable).
# Step() (Stage 5) accepts lists of scorers and objectives, runs them,
# combines their outputs.  Users can register new scorers/objectives
# without touching the framework.
#
# Three default scorers cover the distinct readings of "useful wedge":
#   - entropy_of_four_cell:   Shannon entropy of the K-pair's 4-cell
#                              distribution across things (p-probes-are-
#                              half-spaces — measures discrimination)
#   - boolean_earning_corpus: both off-diagonal cells populated
#                              (p-boolean-earned-by-both-off-diagonals)
#   - oracle_boolean_witness: oracle thing-pairs discriminated
#                              asymmetrically (d-oracle-calibrates-not-gates)
#
# Two default objectives:
#   - oracle_pairs_with_witness: count of oracle pairs with any Boolean-
#     earning K-pair witness (readable, not a gate)
#   - pool_entropy_marginals:    sum of per-K marginal entropies; a
#     total-information objective cheap enough to compute per step
#
# Composite scorer lets users combine defaults with weights, matching
# "Multiple objectives can be evaluated per iteration; their gradients
#  can be combined as weighted sums" from d-weight-objective-pluggable.

from typing import Callable

# Protocol types
Scorer = Callable[["State", "K", "K"], float]
Objective = Callable[["State"], float]


# -- Primitive helpers for counting K-firings across things ----------------


def _count_four_cell(state: "State", k_i: "K", k_j: "K",
                     channel: str = "tau") -> Tuple[int, int, int, int]:
    """Return (n_00, n_01, n_10, n_11): counts of things in each cell of
    the 2×2 (K_i, K_j) joint firing distribution on the given channel.

    Under d-tau-sigma-symmetric-at-grade-1 and atoms with τ=σ, the
    ``tau`` and ``sigma`` channels produce identical counts at grade 1.
    The parameter allows asymmetric analysis at higher grades."""
    idx_i = state.pool.bit_of(k_i)
    idx_j = state.pool.bit_of(k_j)
    if idx_i is None or idx_j is None:
        return (0, 0, 0, 0)
    n = [0, 0, 0, 0]
    for _tid, thing in state.things:
        mask = thing.tau_mask if channel == "tau" else thing.sigma_mask
        bi = (mask >> idx_i) & 1
        bj = (mask >> idx_j) & 1
        # Cell code: bit_i as high bit, bit_j as low bit
        cell = (bi << 1) | bj
        n[cell] += 1
    return tuple(n)


# -- Default scorers --------------------------------------------------------


def scorer_entropy_of_four_cell(state: "State", k_i: "K", k_j: "K") -> float:
    """Shannon entropy (bits) of the K-pair's 4-cell distribution.

    Range: 0 (one cell holds all things) to 2 bits (uniform).  Higher
    entropy = the K-pair carves the thing-pool more evenly into the
    four cells, which (under p-probes-are-half-spaces) suggests
    more compositional information content.
    """
    import math
    cells = _count_four_cell(state, k_i, k_j)
    total = sum(cells)
    if total == 0:
        return 0.0
    ent = 0.0
    for n in cells:
        if n > 0:
            p = n / total
            ent -= p * math.log2(p)
    return ent


def scorer_boolean_earning_corpus(state: "State", k_i: "K", k_j: "K") -> float:
    """Corpus-level Boolean-earning test (p-boolean-earned-by-both-off-
    diagonals).  Returns log(n_01 · n_10) when both off-diagonal cells
    are populated; 0 when either is empty (not Boolean-earning).

    The logarithmic scaling rewards K-pairs whose asymmetric cells are
    BOTH well-populated, over those where one off-diagonal dominates.
    """
    import math
    _, n_01, n_10, _ = _count_four_cell(state, k_i, k_j)
    if n_01 == 0 or n_10 == 0:
        return 0.0
    return math.log(n_01) + math.log(n_10)


def scorer_oracle_boolean_witness(state: "State", k_i: "K", k_j: "K") -> float:
    """Count oracle thing-pairs (A, B) that this K-pair Boolean-earns.

    A thing-pair (A, B) is Boolean-earned by (K_i, K_j) iff one thing
    fires K_i but not K_j AND the other fires K_j but not K_i — i.e.,
    (A, B) occupy opposite off-diagonals of the K-pair's joint
    distribution.  Either orientation counts.

    This scorer directly measures the K-pair's usefulness for
    discriminating oracle-aligned thing-pairs.  Under d-oracle-
    calibrates-not-gates this is a signal, not a gate — it weights
    articulation preference, not commit admission.
    """
    idx_i = state.pool.bit_of(k_i)
    idx_j = state.pool.bit_of(k_j)
    if idx_i is None or idx_j is None:
        return 0.0
    things_dict = dict(state.things)
    count = 0
    for pair in state.oracle_pairs:
        if len(pair) != 2:
            continue
        a_id, b_id = list(pair)
        a = things_dict.get(a_id)
        b = things_dict.get(b_id)
        if a is None or b is None:
            continue
        bi_a = (a.tau_mask >> idx_i) & 1
        bj_a = (a.tau_mask >> idx_j) & 1
        bi_b = (b.tau_mask >> idx_i) & 1
        bj_b = (b.tau_mask >> idx_j) & 1
        # Boolean-earning patterns: A=(1,0) B=(0,1) or A=(0,1) B=(1,0)
        if (bi_a, bj_a, bi_b, bj_b) in {(1, 0, 0, 1), (0, 1, 1, 0)}:
            count += 1
    return float(count)


# -- Default objectives -----------------------------------------------------


def objective_oracle_pairs_with_witness(state: "State") -> float:
    """Count oracle thing-pairs for which ANY K in the pool fires on
    one thing but not the other.  This is a Boolean-earning existence
    test against the pool's CURRENT discriminative power.

    Under p-alignment-is-distribution this is an informational
    read-out, not a commit threshold.  A pair with witness exists =
    the pool can tell the pair apart on some K.  A pair without
    witness = the pool can't discriminate — candidates for wedge
    articulation.

    Implementation: for each oracle pair, compute bitwise
    (a.tau & ~b.tau) and (~a.tau & b.tau); pair has witness iff
    both bitmasks are non-zero.
    """
    things_dict = dict(state.things)
    count = 0
    for pair in state.oracle_pairs:
        if len(pair) != 2:
            continue
        a_id, b_id = list(pair)
        a = things_dict.get(a_id)
        b = things_dict.get(b_id)
        if a is None or b is None:
            continue
        a_only = a.tau_mask & ~b.tau_mask
        b_only = ~a.tau_mask & b.tau_mask
        if a_only and b_only:
            count += 1
    return float(count)


def objective_pool_entropy_marginals(state: "State") -> float:
    """Sum of per-K marginal entropies (firing-vs-gapping balance).

    For each K in the pool, compute the entropy of its firing
    distribution across things — a bit that's balanced near 50%
    contributes near 1 bit; a bit that fires on everyone or no one
    contributes 0.  Sum across pool.

    Maximizing this objective corresponds to configuring weights
    toward K's that maximally discriminate — not necessarily the
    ones closest to an oracle signal.  Contrasts with
    ``objective_oracle_pairs_with_witness``, which emphasizes the
    oracle.  Composing them (with weights) lets step() balance
    general discrimination against oracle-specific discrimination.
    """
    import math
    n_things = len(state.things)
    if n_things == 0:
        return 0.0
    total = 0.0
    for k in state.pool.ks:
        idx = state.pool.bit_of(k)
        if idx is None:
            continue
        n_fires = sum(
            1 for _tid, t in state.things if (t.tau_mask >> idx) & 1
        )
        p = n_fires / n_things
        if 0 < p < 1:
            total += -p * math.log2(p) - (1 - p) * math.log2(1 - p)
    return total


# -- Composite combinator --------------------------------------------------


def compose_scorers(*weighted: Tuple[float, Scorer]) -> Scorer:
    """Build a scorer from (weight, scorer) pairs, weighted sum.

    Matches d-articulation-scorer-pluggable: 'Multiple scorers can run
    simultaneously... their gradients can be combined as weighted sums.
    No single scorer is privileged by the framework.'
    """
    def _composite(state: "State", k_i: "K", k_j: "K") -> float:
        return sum(w * s(state, k_i, k_j) for w, s in weighted)
    return _composite


def compose_objectives(*weighted: Tuple[float, Objective]) -> Objective:
    """Build an objective from (weight, objective) pairs, weighted sum."""
    def _composite(state: "State") -> float:
        return sum(w * f(state) for w, f in weighted)
    return _composite


# -- Registries (for CLI / discovery; not privileged by the framework) ----


SCORERS: dict = {
    "entropy_of_four_cell": scorer_entropy_of_four_cell,
    "boolean_earning_corpus": scorer_boolean_earning_corpus,
    "oracle_boolean_witness": scorer_oracle_boolean_witness,
}


OBJECTIVES: dict = {
    "oracle_pairs_with_witness": objective_oracle_pairs_with_witness,
    "pool_entropy_marginals": objective_pool_entropy_marginals,
}


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
    flat = _flatten_wedge_leaves(canon)
    assert flat == tuple(sorted(flat, key=lambda x: x.key())), "canonical form not sorted"

    # p-bijective-hash-consing: K.key() round-trips via JSON
    # for atoms, wedges of atoms, nested wedges, and ZeroK
    tricky = Atom(Observable("has,comma)and(parens:too"))
    assert tricky.key() == json.dumps(tricky.structure())
    # Round-trip: decode → compare structure
    assert json.loads(tricky.key()) == list(tricky.structure())

    # Wedges with tricky observables do not collide:
    #   Wedge(Atom("a,b"), Atom("c"))  vs  Wedge(Atom("a"), Atom("b,c"))
    # Previously (legacy pre-bijective encoding):
    #   "wedge(atom:a,b,atom:c)" vs "wedge(atom:a,atom:b,c)"
    # could be mis-parsed.  Bijective encoding makes them distinct.
    t1 = Wedge(Atom(Observable("a,b")), Atom(Observable("c")))
    t2 = Wedge(Atom(Observable("a")), Atom(Observable("b,c")))
    assert t1.key() != t2.key(), (
        "bijective encoding must distinguish Wedge(Atom('a,b'), Atom('c')) "
        "from Wedge(Atom('a'), Atom('b,c'))"
    )
    # And each round-trips:
    assert json.loads(t1.key()) == list(t1.structure()) or (
        # JSON arrays decode to lists, our structure is tuples — normalize for comparison
        _tuples_eq_lists(t1.structure(), json.loads(t1.key()))
    )
    assert _tuples_eq_lists(t2.structure(), json.loads(t2.key()))
    # ZeroK round-trips
    assert _tuples_eq_lists(ZeroK().structure(), json.loads(ZeroK().key()))

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
            matching = [
                t for tid, t in state.things if tid.startswith(f"{src}:")
            ]
            for t in matching:
                assert (t.tau_mask >> idx) & 1, (
                    f"thing of source {src!r} does not fire source atom"
                )

        # p-yoneda-identity: kind_at_root probes exist and fire selectively.
        # A thing whose top-level kind is K fires kind_at_root:K but things
        # that only CONTAIN K in their subtree do not fire it.
        for src in available:
            things_of_src = [t for tid, t in state.things if tid.startswith(f"{src}:")]
            if not things_of_src:
                continue
            # Pick a sample thing; verify kind_at_root matches its ThingId
            sample = things_of_src[0]
            # Extract kind from tid like "agda:module:CSTZ.All..." → "module"
            parts = sample.id.split(":", 3)
            if len(parts) >= 2:
                expected_kind = parts[1]
                kr_atom = Atom(Observable(f"kind_at_root:{expected_kind}"))
                kr_idx = state.pool.bit_of(kr_atom)
                assert kr_idx is not None, (
                    f"kind_at_root:{expected_kind} atom not in pool"
                )
                assert (sample.tau_mask >> kr_idx) & 1, (
                    f"sample thing does not fire its kind_at_root probe"
                )

        # p-yoneda-identity: path probes exist (at least the source-root component)
        # e.g. 'agda', 'paper', 'src' should be path probes registered from
        # the first path component of each thing's source_path.
        expected_roots = {"paper": "paper", "agda": "agda", "python": "src"}
        for src in available:
            root = expected_roots.get(src)
            if root is None:
                continue
            path_atom = Atom(Observable(f"path:{root}"))
            idx = state.pool.bit_of(path_atom)
            assert idx is not None, f"path:{root} atom not in pool"

        # p-yoneda-identity: name probes exist for named things
        named_count = sum(
            1 for k in state.pool.ks
            if isinstance(k, Atom) and k.observable.startswith("name:")
        )
        assert named_count > 0, "no name: probes were registered"

        # -- Stage 4: scorer / objective protocols --------------------------
        # Pick two K's that are likely to be informative: a source atom
        # and a kind_at_root atom.
        if state.pool.size() >= 2:
            k_src_candidates = [k for k in state.pool.ks
                                 if isinstance(k, Atom)
                                 and k.observable.startswith("source:")]
            k_kind_candidates = [k for k in state.pool.ks
                                  if isinstance(k, Atom)
                                  and k.observable.startswith("kind_at_root:")]
            if k_src_candidates and k_kind_candidates:
                k_i = k_src_candidates[0]
                k_j = k_kind_candidates[0]

                # Each default scorer returns a finite float
                import math as _math
                for name, fn in SCORERS.items():
                    v = fn(state, k_i, k_j)
                    assert isinstance(v, float), (
                        f"scorer {name!r} did not return a float"
                    )
                    assert _math.isfinite(v), (
                        f"scorer {name!r} returned non-finite value {v!r}"
                    )

                # entropy scorer on the same K paired with itself
                # gives 0 (the distribution collapses to a single cell
                # by p-extensionality-via-hit: Wedge(k,k) normalizes
                # to ZeroK, which has no firing).  Instead, test on
                # same-K cells directly via _count_four_cell.
                cells_self = _count_four_cell(state, k_i, k_i)
                # A K paired with itself: (0,1) and (1,0) cells are
                # both empty — thing either fires K or not, but can't
                # be asymmetric with itself.
                assert cells_self[1] == 0 and cells_self[2] == 0, (
                    "K with itself should have empty off-diagonals"
                )

                # Default objectives return finite floats
                for name, fn in OBJECTIVES.items():
                    v = fn(state)
                    assert isinstance(v, float), (
                        f"objective {name!r} did not return a float"
                    )
                    assert _math.isfinite(v), (
                        f"objective {name!r} returned non-finite value {v!r}"
                    )

                # Composite scorer sums correctly
                composite = compose_scorers(
                    (0.5, scorer_entropy_of_four_cell),
                    (1.0, scorer_boolean_earning_corpus),
                )
                expected = (
                    0.5 * scorer_entropy_of_four_cell(state, k_i, k_j)
                    + 1.0 * scorer_boolean_earning_corpus(state, k_i, k_j)
                )
                got = composite(state, k_i, k_j)
                assert abs(got - expected) < 1e-9, (
                    f"composite scorer arithmetic mismatch: {got} vs {expected}"
                )

                # Composite objective similarly
                comp_obj = compose_objectives(
                    (1.0, objective_oracle_pairs_with_witness),
                    (0.1, objective_pool_entropy_marginals),
                )
                comp_val = comp_obj(state)
                assert _math.isfinite(comp_val), "composite objective non-finite"

                print(f"    Stage 4 scorers/objectives: all registry entries "
                      f"returned finite floats on extracted state")

        # Pool invariant: every observable appears as an Atom K
        for k in state.pool.ks:
            assert isinstance(k, Atom), (
                f"Stage-3 initial pool should contain only Atoms, got {type(k).__name__}"
            )

        print(f"    Stage 3 extraction: {len(state.things)} things, "
              f"{state.pool.size()} atoms, {len(state.oracle_pairs)} oracle pairs")
    else:
        print("    Stage 3 extraction: no source dirs found in cwd; skipping")

    print("Stage 1 + 2 + 2.5 + 2.6 + 3 + 3.5 + 3.6 + 4 smoke test: all assertions passed")
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
