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
import math
import sys
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterator, NewType, Protocol, Tuple

import numpy as np


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


@dataclass(frozen=True, eq=False)
class Thing:
    """A pooled object, identified solely by an opaque ThingId.

    The algebra sees ONLY the identity and the bitmaps.  Under
    ``p-source-is-a-k`` and ``p-no-bespoke-recognition``, source
    provenance is not a privileged field of Thing — it is an
    observable K registered in the Pool.  Same for display names,
    paths, line numbers, and anything else an extractor might want
    to surface.  There is no "metadata" category: every observable
    is a K; reports are queries over the pool + bitmaps.

    ``tau_mask`` and ``sigma_mask`` are np.ndarray(dtype=bool) over
    the Pool: element i True iff the K at pool position i fires on
    this thing in the respective channel.  ``kappa_mask`` is derived
    as ``tau XOR sigma`` by construction (never stored).

    Under p-numpy-is-the-natural-cpu-representation + p-refactor-debt-
    paid-eagerly, Stage 7.0 converted these from Python int bitmasks
    to numpy bool arrays.  This keeps the algebra array-native from
    end to end, consistent with the upcoming HDF5 I/O (Stage 7.1) and
    with the general direction of the framework's CPU representation.

    Immutability: dataclass is frozen, and bitmasks are marked
    read-only at construction time (setflags(write=False)) so the
    frozen invariant extends to the array contents.  Custom __eq__
    and __hash__ are defined because numpy arrays don't compare
    element-wise for boolean equality nor hash — we compare shapes
    + values and hash on .tobytes().
    """

    id: ThingId              # opaque identity; not interpreted by algebra
    tau_mask: np.ndarray     # dtype=bool, length pool_size
    sigma_mask: np.ndarray   # dtype=bool, length pool_size

    def __post_init__(self) -> None:
        # Ensure ndarrays of bool; freeze them against mutation
        for field_name in ("tau_mask", "sigma_mask"):
            arr = getattr(self, field_name)
            if not isinstance(arr, np.ndarray):
                arr = np.asarray(arr, dtype=bool)
                object.__setattr__(self, field_name, arr)
            elif arr.dtype != bool:
                arr = arr.astype(bool)
                object.__setattr__(self, field_name, arr)
            # Make read-only
            arr.setflags(write=False)
        # Invariant: tau_mask and sigma_mask have the same length
        if self.tau_mask.shape != self.sigma_mask.shape:
            raise ValueError(
                f"Thing {self.id!r}: tau_mask shape {self.tau_mask.shape} "
                f"!= sigma_mask shape {self.sigma_mask.shape}"
            )

    def __eq__(self, other) -> bool:
        if not isinstance(other, Thing):
            return False
        return (
            self.id == other.id
            and self.tau_mask.shape == other.tau_mask.shape
            and np.array_equal(self.tau_mask, other.tau_mask)
            and np.array_equal(self.sigma_mask, other.sigma_mask)
        )

    def __hash__(self) -> int:
        return hash((
            self.id,
            self.tau_mask.shape,
            self.tau_mask.tobytes(),
            self.sigma_mask.tobytes(),
        ))

    @property
    def kappa_mask(self) -> np.ndarray:
        """κ-mask by GF(2) XOR of τ and σ.  Derived; never stored.
        Returned array is fresh; caller owns mutation rights."""
        return np.logical_xor(self.tau_mask, self.sigma_mask)

    def fires(self, pool: Pool, k: K, channel: str = "tau") -> bool:
        idx = pool.bit_of(k)
        if idx is None:
            return False
        mask = self.tau_mask if channel == "tau" else (
            self.sigma_mask if channel == "sigma" else self.kappa_mask
        )
        if idx >= len(mask):
            return False
        return bool(mask[idx])

    def tausigma_at(self, pool: Pool, k: K) -> TauSigma:
        """Read the TauSigma state of a specific K on this thing."""
        idx = pool.bit_of(k)
        if idx is None or idx >= len(self.tau_mask):
            return TauSigma(0, 0)
        return TauSigma(
            tau=int(self.tau_mask[idx]),
            sigma=int(self.sigma_mask[idx]),
        )

    def remap(self, old_pool: Pool, new_pool: Pool) -> "Thing":
        """Return this Thing with its bitmaps remapped from old_pool's
        bit indexing to new_pool's bit indexing.

        Used by ``State.merge`` when two shards have divergent pools:
        self.pool bit-indices may not match the merged pool's, so
        Things from self need each bit remapped via K-key lookup.
        """
        if old_pool is new_pool and len(self.tau_mask) == new_pool.size():
            return self
        new_tau = np.zeros(new_pool.size(), dtype=bool)
        new_sigma = np.zeros(new_pool.size(), dtype=bool)
        n_old = len(self.tau_mask)
        for old_idx, k in enumerate(old_pool.ks):
            if old_idx >= n_old:
                break
            new_idx = new_pool.bit_of(k)
            if new_idx is None:
                continue  # K dropped in new pool
            new_tau[new_idx] = self.tau_mask[old_idx]
            new_sigma[new_idx] = self.sigma_mask[old_idx]
        return Thing(id=self.id, tau_mask=new_tau, sigma_mask=new_sigma)

    @staticmethod
    def with_empty_masks(tid: "ThingId", pool_size: int) -> "Thing":
        """Helper: construct a Thing with all-False masks of the
        requested length.  Used in tests and as a default form."""
        empty = np.zeros(pool_size, dtype=bool)
        return Thing(id=tid, tau_mask=empty.copy(), sigma_mask=empty.copy())


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
    # probes for each Thing's identity components.  Under p-numpy-is-
    # the-natural-cpu-representation, masks are np.ndarray(dtype=bool)
    # of length pool.size().
    pool_size = pool.size()
    things: list = []
    for tid, src, obs, identity in raw:
        mask = np.zeros(pool_size, dtype=bool)
        # Subtree kind observations
        for observation in obs:
            idx = pool.bit_of(Atom(Observable(observation)))
            if idx is not None:
                mask[idx] = True
        # Source atom
        src_idx = pool.bit_of(Atom(Observable(f"source:{src}")))
        if src_idx is not None:
            mask[src_idx] = True
        # kind_at_root atom
        kroot_idx = pool.bit_of(
            Atom(Observable(f"kind_at_root:{identity['kind_at_root']}"))
        )
        if kroot_idx is not None:
            mask[kroot_idx] = True
        # path: component atoms
        for pc in identity["path_components"]:
            p_idx = pool.bit_of(Atom(Observable(f"path:{pc}")))
            if p_idx is not None:
                mask[p_idx] = True
        # name:verbatim atom (if named)
        if identity["name_verbatim"]:
            n_idx = pool.bit_of(
                Atom(Observable(f"name:{identity['name_verbatim']}"))
            )
            if n_idx is not None:
                mask[n_idx] = True
        # τ = σ at grade 1; both masks are the same array data (use
        # .copy() to keep them independent since Thing may freeze them
        # separately)
        things.append(
            Thing(id=ThingId(tid), tau_mask=mask.copy(), sigma_mask=mask.copy())
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

# Decomposed signature types (p-type-theory-everywhere): the return
# values of scorers and objectives get distinct NewType wrappers so a
# static checker can catch cross-category misuse (even though at
# runtime they are both float).  Units per scorer class are documented
# on the class; a future tightening could make units part of the
# return-type taxonomy.
ScoreValue = NewType("ScoreValue", float)
ObjectiveValue = NewType("ObjectiveValue", float)


class Scorer(Protocol):
    """A scorer evaluates a candidate wedge K_left ∧ K_right against
    the current State.  Returns a ScoreValue (higher = more useful).

    Every Scorer implementation MUST carry a structural identity
    (``structure`` property) per p-functions-have-structural-identity
    so it survives pickling (p-embarrassingly-parallel), logging
    (trajectory records), and cross-session merging.  The structure
    tuple is bijective: composite scorers recurse into their
    components' structures.
    """

    def __call__(self, state: "State",
                 k_left: "K", k_right: "K") -> ScoreValue: ...

    @property
    def structure(self) -> tuple: ...


class Objective(Protocol):
    """An objective evaluates the current State.  Returns an
    ObjectiveValue the weight-update direction tunes to maximize.
    Same structural-identity requirement as Scorer."""

    def __call__(self, state: "State") -> ObjectiveValue: ...

    @property
    def structure(self) -> tuple: ...


# -- Overlap-demand primitive (used by Stage 5 articulation rule) ----------


def joint_already_captured(state: "State", k_i: "K", k_j: "K") -> bool:
    """Return True iff the pool already contains a K whose firing pattern
    equals K_i ∧ K_j — the wedge is already extensionally in the pool.

    Under ``p-overlap-demands-wedge-articulation`` and
    ``p-extensionality-via-hit``, the wedge K_i ∧ K_j normalizes to a
    canonical representative; the question is whether that canonical
    representative is already registered.  This check uses the pool's
    extensional identity (``Pool.bit_of(Wedge(k_i, k_j))`` — where
    ``bit_of`` internally normalizes before lookup).

    A True return means n_11 observations do NOT demand a new wedge
    (the joint is already captured).  False means the overlap demands
    articulation.  ZeroK-normalized wedges (k_i == k_j after
    normalize; nilpotency) are treated as 'captured' since the zero
    element adds no discrimination.
    """
    candidate = Wedge(k_i, k_j).normalize()
    if isinstance(candidate, ZeroK):
        return True  # nilpotent; no new information possible
    return state.pool.bit_of(candidate) is not None


# -- Primitive helpers for counting K-firings across things ----------------


def _count_four_cell(state: "State", k_i: "K", k_j: "K",
                     channel: str = "tau") -> Tuple[int, int, int, int]:
    """Return (n_00, n_01, n_10, n_11): counts of things in each cell of
    the 2×2 (K_i, K_j) joint firing distribution on the given channel.

    Uses numpy bitwise operations on the per-thing τ/σ arrays — each
    thing's mask is a bool array of length pool_size; extract indices
    i and j across all things gives two bool arrays of length
    n_things; cell counts are sums over bitwise AND / AND-NOT
    combinations.

    Under d-tau-sigma-symmetric-at-grade-1 and atoms with τ=σ, the
    ``tau`` and ``sigma`` channels produce identical counts at grade 1.
    """
    idx_i = state.pool.bit_of(k_i)
    idx_j = state.pool.bit_of(k_j)
    if idx_i is None or idx_j is None:
        return (0, 0, 0, 0)
    fires_i_list = []
    fires_j_list = []
    for _tid, thing in state.things:
        mask = thing.tau_mask if channel == "tau" else thing.sigma_mask
        if idx_i < len(mask):
            fires_i_list.append(bool(mask[idx_i]))
        else:
            fires_i_list.append(False)
        if idx_j < len(mask):
            fires_j_list.append(bool(mask[idx_j]))
        else:
            fires_j_list.append(False)
    fires_i = np.asarray(fires_i_list, dtype=bool)
    fires_j = np.asarray(fires_j_list, dtype=bool)
    n_11 = int(np.sum(fires_i & fires_j))
    n_10 = int(np.sum(fires_i & ~fires_j))
    n_01 = int(np.sum(~fires_i & fires_j))
    n_00 = int(len(fires_i) - n_11 - n_10 - n_01)
    return (n_00, n_01, n_10, n_11)


# -- Default scorers (structural dataclass classes + singletons) ----------


@dataclass(frozen=True)
class XorOffDiagonalScorer:
    """Score = n_01 + n_10 (count of things where exactly one K fires).

    Principled default per p-four-cell-xor-score.  Units: counts.
    Only off-diagonal cells contribute; gap-gap (n_00) and both-fire
    (n_11) contribute zero.
    """
    units: str = "count"

    def __call__(self, state: "State", k_left: "K", k_right: "K") -> ScoreValue:
        _, n_01, n_10, _ = _count_four_cell(state, k_left, k_right)
        return ScoreValue(float(n_01 + n_10))

    @property
    def structure(self) -> tuple:
        return ("scorer", "xor_off_diagonal")


@dataclass(frozen=True)
class XorOffDiagonalLogPairScorer:
    """Score = log(n_01) + log(n_10) when BOTH off-diagonals populated,
    else 0.  Rewards K-pairs whose asymmetric cells are BOTH well-
    populated (p-boolean-earned-by-both-off-diagonals), rather than
    just summing off-diagonals indifferently.  Units: nats (ln)."""
    units: str = "nats"

    def __call__(self, state: "State", k_left: "K", k_right: "K") -> ScoreValue:
        _, n_01, n_10, _ = _count_four_cell(state, k_left, k_right)
        if n_01 == 0 or n_10 == 0:
            return ScoreValue(0.0)
        return ScoreValue(math.log(n_01) + math.log(n_10))

    @property
    def structure(self) -> tuple:
        return ("scorer", "xor_off_diagonal_log_pair")


@dataclass(frozen=True)
class EntropyOfFourCellScorer:
    """Shannon entropy (bits) of the 4-cell CATEGORICAL distribution
    including gap-gap and both-fire cells.  DIAGNOSTIC statistic only:
    conflates gap with overlap and is NOT principled for articulation
    ranking (see p-four-cell-xor-score).  Retained for characterization
    and debugging.  Units: bits.
    """
    units: str = "bits"

    def __call__(self, state: "State", k_left: "K", k_right: "K") -> ScoreValue:
        cells = _count_four_cell(state, k_left, k_right)
        total = sum(cells)
        if total == 0:
            return ScoreValue(0.0)
        ent = 0.0
        for n in cells:
            if n > 0:
                p = n / total
                ent -= p * math.log2(p)
        return ScoreValue(ent)

    @property
    def structure(self) -> tuple:
        return ("scorer", "entropy_of_four_cell")


@dataclass(frozen=True)
class OracleBooleanWitnessTauSigmaScorer:
    """Count oracle thing-pairs (A, B) where A occupies (K_left=1,
    K_right=0) and B occupies (K_left=0, K_right=1) — the τ-σ
    orientation of the Boolean-earning witness pattern.

    Splitting by orientation per p-tau-sigma-not-opposite: the two
    orientations are distinct discriminative patterns.  Collapsing
    them (as Stage 4.5's combined scorer did) was acceptable under
    p-chirality-only-for-higher-valence but forecloses
    chirality-sensitive analysis at higher grades.  Units: counts.
    """
    units: str = "count"

    def __call__(self, state: "State", k_left: "K", k_right: "K") -> ScoreValue:
        idx_i = state.pool.bit_of(k_left)
        idx_j = state.pool.bit_of(k_right)
        if idx_i is None or idx_j is None:
            return ScoreValue(0.0)
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
            bi_a = int(a.tau_mask[idx_i]) if idx_i < len(a.tau_mask) else 0
            bj_a = int(a.tau_mask[idx_j]) if idx_j < len(a.tau_mask) else 0
            bi_b = int(b.tau_mask[idx_i]) if idx_i < len(b.tau_mask) else 0
            bj_b = int(b.tau_mask[idx_j]) if idx_j < len(b.tau_mask) else 0
            # τ-σ orientation: A=(1,0), B=(0,1)
            if (bi_a, bj_a, bi_b, bj_b) == (1, 0, 0, 1):
                count += 1
        return ScoreValue(float(count))

    @property
    def structure(self) -> tuple:
        return ("scorer", "oracle_boolean_witness_tau_sigma")


@dataclass(frozen=True)
class OracleBooleanWitnessSigmaTauScorer:
    """Count oracle thing-pairs (A, B) where A occupies (K_left=0,
    K_right=1) and B occupies (K_left=1, K_right=0) — the σ-τ
    orientation, the opposite chirality from
    OracleBooleanWitnessTauSigmaScorer.  Units: counts.
    """
    units: str = "count"

    def __call__(self, state: "State", k_left: "K", k_right: "K") -> ScoreValue:
        idx_i = state.pool.bit_of(k_left)
        idx_j = state.pool.bit_of(k_right)
        if idx_i is None or idx_j is None:
            return ScoreValue(0.0)
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
            bi_a = int(a.tau_mask[idx_i]) if idx_i < len(a.tau_mask) else 0
            bj_a = int(a.tau_mask[idx_j]) if idx_j < len(a.tau_mask) else 0
            bi_b = int(b.tau_mask[idx_i]) if idx_i < len(b.tau_mask) else 0
            bj_b = int(b.tau_mask[idx_j]) if idx_j < len(b.tau_mask) else 0
            # σ-τ orientation: A=(0,1), B=(1,0)
            if (bi_a, bj_a, bi_b, bj_b) == (0, 1, 1, 0):
                count += 1
        return ScoreValue(float(count))

    @property
    def structure(self) -> tuple:
        return ("scorer", "oracle_boolean_witness_sigma_tau")


# Singletons for call-site continuity with prior stages' function names
scorer_xor_off_diagonal = XorOffDiagonalScorer()
scorer_xor_off_diagonal_log_pair = XorOffDiagonalLogPairScorer()
scorer_boolean_earning_corpus = scorer_xor_off_diagonal_log_pair  # alias
scorer_entropy_of_four_cell = EntropyOfFourCellScorer()
scorer_oracle_boolean_witness_tau_sigma = OracleBooleanWitnessTauSigmaScorer()
scorer_oracle_boolean_witness_sigma_tau = OracleBooleanWitnessSigmaTauScorer()


# -- Default objectives (structural dataclass classes + singletons) -------


@dataclass(frozen=True)
class OraclePairsWithWitnessObjective:
    """Count oracle thing-pairs for which the pool carries ANY witness
    (some K fires on one thing but not the other).  Under p-alignment-
    is-distribution this is informational, not a commit threshold.
    Units: counts.
    """
    units: str = "count"

    def __call__(self, state: "State") -> ObjectiveValue:
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
            # Align mask lengths (in case a, b come from different
            # pool snapshots — shouldn't happen within a single
            # State, but defend)
            n = min(len(a.tau_mask), len(b.tau_mask))
            ta = a.tau_mask[:n]
            tb = b.tau_mask[:n]
            a_only = ta & ~tb
            b_only = ~ta & tb
            if np.any(a_only) and np.any(b_only):
                count += 1
        return ObjectiveValue(float(count))

    @property
    def structure(self) -> tuple:
        return ("objective", "oracle_pairs_with_witness")


@dataclass(frozen=True)
class PoolEntropyMarginalsObjective:
    """Sum of per-K marginal firing entropies.  Emphasizes
    configurations where K's fire with balanced frequency across
    things (p-probes-are-half-spaces — balanced half-spaces carry
    more discrimination).  Units: bits.
    """
    units: str = "bits"

    def __call__(self, state: "State") -> ObjectiveValue:
        n_things = len(state.things)
        if n_things == 0:
            return ObjectiveValue(0.0)
        total = 0.0
        for k in state.pool.ks:
            idx = state.pool.bit_of(k)
            if idx is None:
                continue
            n_fires = 0
            for _tid, t in state.things:
                if idx < len(t.tau_mask) and t.tau_mask[idx]:
                    n_fires += 1
            p = n_fires / n_things
            if 0 < p < 1:
                total += -p * math.log2(p) - (1 - p) * math.log2(1 - p)
        return ObjectiveValue(total)

    @property
    def structure(self) -> tuple:
        return ("objective", "pool_entropy_marginals")


# Singletons for call-site continuity
objective_oracle_pairs_with_witness = OraclePairsWithWitnessObjective()
objective_pool_entropy_marginals = PoolEntropyMarginalsObjective()


# -- Composite combinators (frozen dataclasses with structural identity) --


@dataclass(frozen=True)
class CompositeScorer:
    """Weighted sum of component scorers.  Per p-functions-have-
    structural-identity, this is a frozen dataclass (not a closure)
    so the composite survives pickling, logging, and cross-session
    merging.  Its ``structure`` tuple recurses into components'
    structures — bijective identity across the tree."""
    components: Tuple[Tuple[float, Scorer], ...]

    def __call__(self, state: "State",
                 k_left: "K", k_right: "K") -> ScoreValue:
        total = 0.0
        for w, s in self.components:
            total += w * s(state, k_left, k_right)
        return ScoreValue(total)

    @property
    def structure(self) -> tuple:
        return ("composite_scorer",
                tuple((w, s.structure) for w, s in self.components))


@dataclass(frozen=True)
class CompositeObjective:
    """Weighted sum of component objectives; structural identity
    mirrors CompositeScorer."""
    components: Tuple[Tuple[float, Objective], ...]

    def __call__(self, state: "State") -> ObjectiveValue:
        total = 0.0
        for w, f in self.components:
            total += w * f(state)
        return ObjectiveValue(total)

    @property
    def structure(self) -> tuple:
        return ("composite_objective",
                tuple((w, f.structure) for w, f in self.components))


def compose_scorers(*weighted: Tuple[float, Scorer]) -> CompositeScorer:
    """Construct a CompositeScorer from (weight, scorer) pairs.  Kept
    as a factory function for call-site ergonomics; returns a frozen
    dataclass, not a closure."""
    return CompositeScorer(components=tuple(weighted))


def compose_objectives(*weighted: Tuple[float, Objective]) -> CompositeObjective:
    """Construct a CompositeObjective from (weight, objective) pairs."""
    return CompositeObjective(components=tuple(weighted))


# -- Registries (for CLI / discovery; not privileged by the framework) ----


# The orientation-union scorer, as a composite of the two orientation
# scorers, for callers who want Stage 4.5's combined behavior.  Identity
# is structural (via CompositeScorer) — not anonymous.
scorer_oracle_boolean_witness_union = compose_scorers(
    (1.0, scorer_oracle_boolean_witness_tau_sigma),
    (1.0, scorer_oracle_boolean_witness_sigma_tau),
)


SCORERS: dict = {
    # Principled default (p-four-cell-xor-score).
    "xor_off_diagonal": scorer_xor_off_diagonal,
    # Boolean-earning (p-boolean-earned-by-both-off-diagonals).
    "xor_off_diagonal_log_pair": scorer_xor_off_diagonal_log_pair,
    "boolean_earning_corpus": scorer_boolean_earning_corpus,  # alias
    # Oracle orientation-split (p-tau-sigma-not-opposite).
    "oracle_boolean_witness_tau_sigma": scorer_oracle_boolean_witness_tau_sigma,
    "oracle_boolean_witness_sigma_tau": scorer_oracle_boolean_witness_sigma_tau,
    "oracle_boolean_witness_union": scorer_oracle_boolean_witness_union,
    # Diagnostic only (NOT principled for ranking).
    "entropy_of_four_cell": scorer_entropy_of_four_cell,
}


OBJECTIVES: dict = {
    "oracle_pairs_with_witness": objective_oracle_pairs_with_witness,
    "pool_entropy_marginals": objective_pool_entropy_marginals,
}


# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Stage 5 — step() — one closed-loop iteration
# ---------------------------------------------------------------------------
#
# step(state) → state' is the single update rule that together with
# run_to_fixed_point (Stage 6) constitutes the entire closed loop
# (p-closed-self-referential-loop).  Pure function; no mutation of
# input state; merge-compatible (p-embarrassingly-parallel).
#
# The update has two phases (Stage 5.5 removed the third — see
# c-weight-updater-becomes-new-k-articulation):
#
#   1. Deterministic articulation (p-overlap-demands-wedge-articulation):
#      enumerate every K-pair (K_i, K_j) in the current pool where
#      some thing fires both (n_11 > 0) AND the joint Wedge(K_i, K_j)
#      is not yet extensionally present in the pool.  Each such pair
#      DEMANDS articulation.  Articulation adds the wedge K to the
#      pool and extends each thing's τ/σ bitmaps to include the new
#      bit (set iff both parents fire on that thing, per d-wedge-bit-
#      and-of-parents).
#
#      Scorer PROVIDES ORDERING when demand exceeds per-step budget
#      — does NOT gate which demands are ever met (the remainder
#      persists into subsequent steps).
#
#   2. Trajectory logging: an entry recording the iteration's work
#      is appended to state.trajectory.  Entries include scorer and
#      objective structures (p-functions-have-structural-identity)
#      so any wedge's provenance is recoverable from the log.
#
# Weight-tuning via a "WeightUpdater" phase was REMOVED in Stage 5.5
# under p-weight-update-is-new-k-articulation: mutating a K's scalar
# destroys the regime under which earlier wedges were articulated.
# The information-preserving alternative is to articulate NEW K's
# with modified scalars, letting both coexist in the pool.  step()
# therefore does not modify weights; any scalar evolution happens
# as new-K articulation in a future stage.
#
# Performance: per-K firing bitmaps are precomputed ONCE per step,
# converting _count_four_cell-equivalent work from O(n_things) per
# call to O(n_things / 64) ≈ O(1) integer-bitwise ops.  The
# candidate enumeration uses thing-iteration (for each thing, each
# pair of set bits is a pair with n_11 ≥ 1), bounding the candidate
# space to pairs that actually co-fire somewhere.


# -- Precomputation helpers ------------------------------------------------


def _bit_positions(x: int) -> list:
    """Extract set-bit positions from an integer as a list (in
    ascending order)."""
    out = []
    while x:
        lsb = x & -x
        out.append(lsb.bit_length() - 1)
        x &= x - 1
    return out


def _compute_firing_bitmaps(
    pool: "Pool",
    thing_order: list,
    channel: str = "tau",
) -> np.ndarray:
    """Per-K-index firing bitmap over thing-indices, as a 2D numpy
    array of shape ``(pool_size, n_things)`` and dtype=bool.

    This is the TRANSPOSE of the per-thing bitmap storage: ``result[i, j]``
    is True iff the K at pool position i fires on thing j (in the
    requested channel).  Computed once per step() to enable O(1)
    cell counting via numpy bitwise ops + np.sum over rows.

    Under p-numpy-is-the-natural-cpu-representation: this is an
    array-native computation throughout; no Python int bitmask
    intermediate.
    """
    n_pool = pool.size()
    n_things = len(thing_order)
    result = np.zeros((n_pool, n_things), dtype=bool)
    for j, (_tid, thing) in enumerate(thing_order):
        mask = thing.tau_mask if channel == "tau" else thing.sigma_mask
        k = min(len(mask), n_pool)
        # Column j of result := thing's mask up to pool_size positions
        result[:k, j] = mask[:k]
    return result


def _articulate_wedges_batch(
    state: "State",
    wedges: list,
    firing_bitmaps: np.ndarray,
) -> Tuple["State", int]:
    """Articulate a BATCH of wedges into state in one pass.

    Under p-numpy-is-the-natural-cpu-representation + p-refactor-debt-
    paid-eagerly, Stage 7.0 replaced the per-wedge incremental
    mutation of the old ``_articulate_wedge_into_state`` with a
    vectorized batched form.

    For each wedge W, its firing bitmap over things is the AND of
    its leaf atoms' rows in ``firing_bitmaps``
    (d-wedge-bit-and-of-parents).  Compute all new wedge firings as
    a 2D matrix of shape ``(n_new_wedges, n_things)``.  Skip wedges
    whose firing is identically False (degenerate; no discrimination
    added).

    Then extend every thing's τ/σ masks ONCE by concatenating the
    new column(s).  At first appearance, τ = σ for articulated
    wedges per d-wedge-bit-and-of-parents.

    Returns (new_state, count_articulated).  The batched form avoids
    the appearance/reality gap of the previous per-wedge mutation —
    this function truly is a pure transformer.
    """
    thing_order = list(sorted(state.things, key=lambda kv: kv[0]))
    n_things = len(thing_order)

    # For each wedge, compute its firing bitmap as AND of atom rows.
    # Dedup against the EXISTING pool (pool_index) AND against earlier
    # entries in this batch — multiple distinct candidate K-pairs can
    # normalize to the same canonical wedge (e.g., x∧(y∧z), y∧(x∧z),
    # z∧(x∧y) all normalize to x∧y∧z), so without batch-local dedup
    # the pool would be asked to register the same key twice.
    pool_index = {key: idx for key, idx in state.pool.by_key}
    seen_in_batch: set = set()
    kept_wedges = []
    kept_firings = []  # each is a 1D bool array of length n_things
    for wedge in wedges:
        if isinstance(wedge, ZeroK):
            continue
        w_key = wedge.key()
        if w_key in pool_index:
            continue  # already in pool before this batch
        if w_key in seen_in_batch:
            continue  # already queued earlier in this batch
        # Compute firing as AND over leaf atoms
        firing = None
        for atom in wedge.atoms():
            a_idx = state.pool.bit_of(atom)
            if a_idx is None:
                firing = None
                break
            row = firing_bitmaps[a_idx]
            firing = row if firing is None else firing & row
        if firing is None or not np.any(firing):
            continue  # degenerate
        seen_in_batch.add(w_key)
        kept_wedges.append(wedge)
        kept_firings.append(firing)

    if not kept_wedges:
        return state, 0

    # Build new pool by appending each kept wedge
    new_pool = state.pool
    for w in kept_wedges:
        new_pool = new_pool.with_k(w)

    # Stack firings into [n_new, n_things] then transpose to
    # [n_things, n_new] — one column per new wedge
    new_firings_matrix = np.stack(kept_firings, axis=0)  # [n_new, n_things]
    n_new = new_firings_matrix.shape[0]
    per_thing_new_cols = new_firings_matrix.T  # [n_things, n_new]

    # Extend each thing's τ/σ masks: concat old mask + this thing's new columns
    # (at first appearance τ=σ for wedges, so both masks get the same extension)
    new_things: list = []
    for j, (tid, thing) in enumerate(thing_order):
        new_cols = per_thing_new_cols[j]  # [n_new]
        new_tau = np.concatenate([thing.tau_mask, new_cols])
        new_sigma = np.concatenate([thing.sigma_mask, new_cols])
        new_things.append(
            (tid, Thing(id=tid, tau_mask=new_tau, sigma_mask=new_sigma))
        )

    new_state = State(
        pool=new_pool,
        things=tuple(sorted(new_things, key=lambda kv: kv[0])),
        oracle_pairs=state.oracle_pairs,
        weights=state.weights,
        trajectory=state.trajectory,
        iteration=state.iteration,
    )
    return new_state, n_new


# -- step() -----------------------------------------------------------------


def step(
    state: "State",
    *,
    scorer: Scorer | None = None,
    objective: Objective | None = None,
    max_articulations_per_step: int | None = None,
) -> "State":
    """One closed-loop iteration.

    Deterministically identifies demanded wedges (p-overlap-demands-
    wedge-articulation), orders them by the optional scorer, and
    articulates up to ``max_articulations_per_step`` of them (or all
    of them when the budget is ``None``).  Appends a trajectory
    entry.  Returns a new State.

    Pure: no mutation of input state; safe to call concurrently on
    disjoint State shards (p-embarrassingly-parallel).

    ``scorer``: if None, demanded wedges are articulated in
    deterministic wedge-key order.  If present, demanded wedges are
    ordered by score descending, ties broken by wedge key.

    ``objective``: retained in the signature for trajectory logging
    (its structure is recorded so a read-out can reproduce the
    articulation regime).  step() itself does not modify weights —
    weight evolution under p-weight-update-is-new-k-articulation is
    a new-K-articulation concern, not a mutation of existing weights.

    ``max_articulations_per_step``: default None means 'articulate
    every demanded wedge this step'.  A positive integer bounds the
    batch; unmet demand persists into subsequent steps.  The
    framework does not pick a budget; callers do.
    """
    # -- Phase 0: precompute caches -----------------------------------------
    thing_order = list(sorted(state.things, key=lambda kv: kv[0]))
    firing_bitmaps = _compute_firing_bitmaps(state.pool, thing_order)
    pool_index = {key: idx for key, idx in state.pool.by_key}
    n_things = len(thing_order)

    # -- Phase 1: enumerate candidate K-pairs (n_11 > 0) -------------------
    # For each thing, each pair of its set bits (positions where the
    # τ-mask is True) is a K-pair that co-fires on at least this thing
    # (n_11 ≥ 1).  Set-dedup across things.  Uses np.where to extract
    # set-bit indices per thing — vectorized over numpy arrays.
    candidate_pairs: set = set()
    for j, (_tid, thing) in enumerate(thing_order):
        bits = np.where(thing.tau_mask)[0]  # indices of True entries
        n_bits = len(bits)
        for a in range(n_bits):
            bi = int(bits[a])
            for b in range(a + 1, n_bits):
                bj = int(bits[b])
                candidate_pairs.add((bi, bj))

    # -- Phase 2: filter to uncaptured demands -----------------------------
    demanded: list = []  # list of (k_left, k_right, wedge)
    for (i, j) in candidate_pairs:
        k_i = state.pool.ks[i]
        k_j = state.pool.ks[j]
        wedge = Wedge(k_i, k_j).normalize()
        if isinstance(wedge, ZeroK):
            continue
        if wedge.key() in pool_index:
            continue  # captured; no demand
        demanded.append((k_i, k_j, wedge))

    # -- Phase 3: order by scorer (if provided), else by wedge key --------
    need_scoring = (
        scorer is not None
        and max_articulations_per_step is not None
        and len(demanded) > max_articulations_per_step
    )
    if need_scoring:
        scored = []
        for k_i, k_j, wedge in demanded:
            s = scorer(state, k_i, k_j)
            scored.append((s, k_i, k_j, wedge))
        scored.sort(key=lambda x: (-x[0], x[3].key()))
        ordered = [(k_i, k_j, wedge) for _s, k_i, k_j, wedge in scored]
    else:
        demanded.sort(key=lambda x: x[2].key())
        ordered = demanded

    if max_articulations_per_step is None:
        to_articulate = ordered
    else:
        to_articulate = ordered[:max_articulations_per_step]

    # -- Phase 4: articulate (batched under p-numpy-is-the-natural-cpu-
    # representation; single pure transformer, no step-local mutation) ----
    wedges_to_articulate = [w for (_ki, _kj, w) in to_articulate]
    new_state, articulated_count = _articulate_wedges_batch(
        state, wedges_to_articulate, firing_bitmaps
    )

    # -- Phase 5: trajectory entry -----------------------------------------
    # Weight-tuning phase removed per c-weight-updater-becomes-new-k-
    # articulation.  `objective` is retained in the signature so its
    # structural identity is logged — a future new-K-articulation
    # strategy can consult the trajectory to see which objective the
    # operator thought mattered at each step.
    traj_entry = {
        "iteration": state.iteration + 1,
        "demanded_count": len(demanded),
        "articulated_count": articulated_count,
        "pool_size_before": state.pool.size(),
        "pool_size_after": new_state.pool.size(),
        "n_things": n_things,
        "max_articulations_per_step": max_articulations_per_step,
    }
    if scorer is not None:
        traj_entry["scorer"] = list(scorer.structure)
    if objective is not None:
        traj_entry["objective"] = list(objective.structure)

    return new_state.appending_trajectory(traj_entry)


# ---------------------------------------------------------------------------
# Stage 6 — run_to_fixed_point() — closed-loop driver
# ---------------------------------------------------------------------------
#
# run_to_fixed_point(state) iterates step() until the state's signature
# stabilizes — no new wedges were articulated on the last step
# (d-fixed-point-is-termination).  Under p-iteration-count-unknown
# there is NO max_iters parameter: the loop runs until fixed-point,
# however long that takes.  Callers needing a hard bound impose it
# externally; the framework does not.
#
# Since Stage 5.5 removed weight-updating as a framework concern
# (c-weight-updater-becomes-new-k-articulation), the termination
# criterion simplifies to pool stabilization.  State.signature()
# already excludes the trajectory (monotonically growing) and
# iteration counter, so signature equality between successive states
# means exactly: the pool did not grow AND things' bitmaps did not
# change AND oracle pairs didn't shift.  All real progress shows up
# as a signature change; no-progress is the fixed point.
#
# Pure and merge-compatible (p-embarrassingly-parallel): callers can
# run_to_fixed_point on disjoint state shards independently, then
# merge and re-run run_to_fixed_point on the union to settle any
# cross-shard articulations that neither local fixed-point captured.


def run_to_fixed_point(
    state: "State",
    *,
    scorer: Scorer | None = None,
    objective: Objective | None = None,
    max_articulations_per_step: int | None = None,
) -> "State":
    """Iterate step() until the state signature stops changing.

    Termination per d-fixed-point-is-termination: when two successive
    step() invocations produce states with identical signatures, the
    loop has reached a fixed point and the current state is returned.

    No max_iters (p-iteration-count-unknown).  Callers needing a
    budget should either bound max_articulations_per_step (slowing
    each iteration) or wrap this function in their own bounded loop.

    Parameters are forwarded to step() unchanged.

    Pure: does not mutate input state.  Returns the fixed-point state,
    including the full trajectory of every intermediate iteration for
    inspection / replay / p-bijective-hash-consing round-trips.
    """
    while True:
        prev_sig = state.signature()
        state = step(
            state,
            scorer=scorer,
            objective=objective,
            max_articulations_per_step=max_articulations_per_step,
        )
        if state.signature() == prev_sig:
            return state


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

    # Helper: convert an integer bit-pattern to a bool ndarray of
    # given length (smoke-test convenience; production code uses
    # numpy directly).
    def _int_mask(n: int, length: int) -> np.ndarray:
        arr = np.zeros(length, dtype=bool)
        for i in range(length):
            if (n >> i) & 1:
                arr[i] = True
        return arr

    # Thing: κ_mask = τ_mask ⊕ σ_mask; Thing has ONLY id + bitmaps
    t = Thing(id=ThingId("x"),
              tau_mask=_int_mask(0b1010, 4),
              sigma_mask=_int_mask(0b1100, 4))
    # κ_mask is the elementwise XOR of τ and σ: 1010 ⊕ 1100 = 0110
    assert np.array_equal(t.kappa_mask, _int_mask(0b0110, 4))
    # Thing has no source_path/display/line — every observable is a K.
    # If an extractor wants source-path visible to reports, it registers
    # an atomic K (e.g. Atom("source:paper/x.py")) that fires on this
    # Thing's tau bitmap.  No privileged metadata category exists.
    assert not hasattr(t, "source_path"), "Thing should not carry source_path"
    assert not hasattr(t, "display"), "Thing should not carry display"
    assert not hasattr(t, "line"), "Thing should not carry line"

    # tausigma_at reads correctly
    t2 = Thing(id=ThingId("y"),
               tau_mask=_int_mask(0b101, 3),
               sigma_mask=_int_mask(0b011, 3))
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
    t1 = Thing(id=ThingId("A"),
               tau_mask=_int_mask(0b01, 2),
               sigma_mask=_int_mask(0b01, 2))
    t2 = Thing(id=ThingId("B"),
               tau_mask=_int_mask(0b10, 2),
               sigma_mask=_int_mask(0b11, 2))
    s1 = State(
        pool=pool_a,
        things=((ThingId("A"), t1),),
        weights=((ak0.key(), 1.5),),
    )

    # Second state uses an extended pool (prefix-compatible)
    pool_b = pool_a.with_k(ak2)
    # t2/t3 masks extend to length 3 to match extended pool
    t2_ext = Thing(id=ThingId("B"),
                   tau_mask=_int_mask(0b10, 3),
                   sigma_mask=_int_mask(0b11, 3))
    t3 = Thing(id=ThingId("C"),
               tau_mask=_int_mask(0b100, 3),
               sigma_mask=_int_mask(0b000, 3))
    s2 = State(
        pool=pool_b,
        things=((ThingId("B"), t2_ext), (ThingId("C"), t3)),
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
    d_thing = Thing.with_empty_masks(ThingId("D"), pool_b.size())
    s3 = State(pool=pool_b, things=((ThingId("D"), d_thing),))
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

    # Shard A sees thing X firing on k0 and k1 → tau_mask = [1,1] over shardA_pool
    thingA_X = Thing(id=ThingId("X"),
                     tau_mask=_int_mask(0b11, 2),
                     sigma_mask=_int_mask(0b11, 2))
    # Shard B sees thing Y firing on k1 and k2 → tau_mask = [1,1] over shardB_pool
    thingB_Y = Thing(id=ThingId("Y"),
                     tau_mask=_int_mask(0b11, 2),
                     sigma_mask=_int_mask(0b11, 2))

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
        # κ = 0 identically for every thing at grade 1 (tau = sigma → xor = False)
        for tid, thing in state.things:
            assert not np.any(thing.kappa_mask), (
                f"thing {tid!r} has κ ≠ 0 at grade 1; τ should equal σ for atoms"
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
                assert idx < len(t.tau_mask) and bool(t.tau_mask[idx]), (
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
                assert kr_idx < len(sample.tau_mask) and bool(sample.tau_mask[kr_idx]), (
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

                # Stage 4.5: p-four-cell-xor-score verification.
                # xor_off_diagonal on a K paired with itself = 0
                # (no off-diagonal firings when the two K's are identical).
                self_score = scorer_xor_off_diagonal(state, k_i, k_i)
                assert self_score == 0.0, (
                    f"K paired with itself should score 0 under XOR "
                    f"(got {self_score})"
                )
                # xor_off_diagonal score equals n_01 + n_10 by construction
                n00, n01, n10, n11 = _count_four_cell(state, k_i, k_j)
                expected_xor = float(n01 + n10)
                got_xor = scorer_xor_off_diagonal(state, k_i, k_j)
                assert abs(got_xor - expected_xor) < 1e-9, (
                    f"xor scorer mismatch: got {got_xor}, expected {expected_xor}"
                )

                # Stage 4.5: joint_already_captured semantics.
                # An atom always captures itself: Wedge(a, a) normalizes to
                # ZeroK (nilpotent), treated as captured.
                assert joint_already_captured(state, k_i, k_i), (
                    "self-wedge should be treated as 'captured' "
                    "(nilpotent ZeroK)"
                )
                # Two distinct atoms whose joint is NOT yet in the pool:
                # overlap demands articulation (joint_already_captured = False).
                # Pick any two atoms that aren't the same.
                if len(k_src_candidates) > 0 and len(k_kind_candidates) > 0:
                    a1 = k_src_candidates[0]
                    a2 = k_kind_candidates[0]
                    # These two atoms haven't been wedged yet in the pool.
                    # The joint is not captured.
                    captured = joint_already_captured(state, a1, a2)
                    assert not captured, (
                        "fresh atom pair should have uncaptured joint "
                        "before any wedge is registered"
                    )

                # Stage 4.6: structural identity on scorers and objectives
                # (p-functions-have-structural-identity)
                for name, s in SCORERS.items():
                    assert hasattr(s, "structure"), (
                        f"scorer {name!r} has no structure property"
                    )
                    struct = s.structure
                    assert isinstance(struct, tuple), (
                        f"scorer {name!r} structure is not a tuple"
                    )
                    # Structure must be bijective-round-trippable via JSON
                    # (though the python nested tuples ≠ json arrays until
                    # reconstructed; the test is that json.dumps succeeds
                    # without raising).
                    try:
                        json.dumps(struct)
                    except TypeError:
                        raise AssertionError(
                            f"scorer {name!r} structure not JSON-serializable: {struct!r}"
                        )

                for name, f in OBJECTIVES.items():
                    assert hasattr(f, "structure")
                    json.dumps(f.structure)

                # Composite scorer carries nested structural identity
                cs = compose_scorers(
                    (0.5, scorer_xor_off_diagonal),
                    (1.0, scorer_boolean_earning_corpus),
                )
                cs_struct = cs.structure
                assert cs_struct[0] == "composite_scorer"
                assert len(cs_struct[1]) == 2  # two components
                # Each component structure is preserved
                assert cs_struct[1][0][0] == 0.5
                assert cs_struct[1][0][1] == ("scorer", "xor_off_diagonal")

                # Stage 4.6: split orientation scorers — τ-σ and σ-τ are
                # distinct per p-tau-sigma-not-opposite.  Their counts
                # sum to the Stage 4.5 combined count.
                tau_sigma_count = scorer_oracle_boolean_witness_tau_sigma(
                    state, k_i, k_j
                )
                sigma_tau_count = scorer_oracle_boolean_witness_sigma_tau(
                    state, k_i, k_j
                )
                union_count = scorer_oracle_boolean_witness_union(
                    state, k_i, k_j
                )
                assert abs(
                    union_count - (tau_sigma_count + sigma_tau_count)
                ) < 1e-9, (
                    f"orientation-union scorer should sum to {tau_sigma_count} "
                    f"+ {sigma_tau_count}, got {union_count}"
                )

                # Structural identity of the union composite recurses
                union_struct = scorer_oracle_boolean_witness_union.structure
                assert union_struct[0] == "composite_scorer"

                # Frozen dataclasses are hashable — can be used as dict keys
                d = {scorer_xor_off_diagonal: "principled"}
                assert d[scorer_xor_off_diagonal] == "principled"

                print(f"    Stage 4 + 4.5 + 4.6 scorers/objectives: structural "
                      f"identity + orientation-split verified on extracted state")

                # -- Stage 5 + 5.5: step() -----------------------------
                # Run one step on the extracted state with a small
                # per-step budget to keep the smoke test fast.
                # (Default None = unlimited, but for the smoke test we
                # prefer a bounded iteration.)
                s0 = state
                s1 = step(
                    s0,
                    scorer=scorer_xor_off_diagonal,
                    objective=objective_oracle_pairs_with_witness,
                    max_articulations_per_step=20,
                )

                # Pool grew by at most 20 wedges
                pool_growth = s1.pool.size() - s0.pool.size()
                assert 0 <= pool_growth <= 20, (
                    f"step() articulated {pool_growth} wedges; "
                    f"expected 0..20"
                )

                # Iteration counter advanced
                assert s1.iteration == s0.iteration + 1, (
                    f"iteration {s0.iteration} → {s1.iteration}; expected +1"
                )

                # Trajectory entry recorded; carries structural identity
                # of scorer / objective / weight_updater
                assert len(s1.trajectory) == len(s0.trajectory) + 1
                last = s1.trajectory[-1]
                assert last["iteration"] == s0.iteration + 1
                assert last["pool_size_before"] == s0.pool.size()
                assert last["pool_size_after"] == s1.pool.size()
                assert last["articulated_count"] == pool_growth
                assert "scorer" in last
                assert last["scorer"][0] == "scorer"
                assert "objective" in last
                # Stage 5.5: no weight_updater field in trajectory
                assert "weight_updater" not in last, (
                    "weight_updater removed per c-weight-updater-becomes-new-k-articulation"
                )

                # Signature changed when pool grew
                if pool_growth > 0:
                    assert s0.signature() != s1.signature(), (
                        "signature should change when pool grew"
                    )

                # Every newly-articulated K is a Wedge (not Atom)
                for k in s1.pool.ks[s0.pool.size():]:
                    assert isinstance(k, Wedge), (
                        f"articulated K {k!r} is not a Wedge"
                    )

                # Each new wedge's firing respects d-wedge-bit-and-of-parents:
                # the wedge fires on a thing iff ALL its atoms fire
                s1_things_dict = dict(s1.things)
                for k in s1.pool.ks[s0.pool.size():]:
                    w_idx = s1.pool.bit_of(k)
                    assert w_idx is not None
                    for _tid, thing in s1.things:
                        wedge_fires = (
                            w_idx < len(thing.tau_mask)
                            and bool(thing.tau_mask[w_idx])
                        )
                        atoms_fire = True
                        for atom in k.atoms():
                            a_idx = s1.pool.bit_of(atom)
                            if a_idx is None:
                                continue
                            if a_idx >= len(thing.tau_mask) or not bool(thing.tau_mask[a_idx]):
                                atoms_fire = False
                                break
                        assert wedge_fires == atoms_fire, (
                            f"wedge {k.key()[:40]!r} firing ≠ AND of atom firings "
                            f"on thing {_tid!r}"
                        )

                # Idempotency under re-articulation: wedges added in s1
                # are captured in s1's pool, so another step on s1 will
                # not re-articulate them.  Run a second step and check
                # the total wedge count does not include duplicates.
                s2 = step(
                    s1,
                    scorer=scorer_xor_off_diagonal,
                    max_articulations_per_step=20,
                )
                # Each wedge key should be unique in the pool
                keys_seen: set = set()
                for k in s2.pool.ks:
                    key = k.key()
                    assert key not in keys_seen, (
                        f"duplicate key in pool: {key[:40]!r}"
                    )
                    keys_seen.add(key)

                # Stage 5.5: exercise σ-channel path.  Under τ=σ atoms
                # σ-firing bitmaps should equal τ-firing bitmaps, but
                # the path must be callable.  This is the structural
                # test of p-tau-sigma-separation — the machinery must
                # exist for σ independently of whether it currently
                # differs from τ in value.
                thing_order_local = list(sorted(state.things, key=lambda kv: kv[0]))
                fires_tau = _compute_firing_bitmaps(
                    state.pool, thing_order_local, channel="tau"
                )
                fires_sigma = _compute_firing_bitmaps(
                    state.pool, thing_order_local, channel="sigma"
                )
                # Under τ=σ atoms, the 2D [pool × things] bitmaps agree
                assert np.array_equal(fires_tau, fires_sigma), (
                    "τ/σ firing bitmaps disagree under supposedly-symmetric atoms"
                )

                # Stage 5.5: default budget is None → articulates all
                # demanded wedges.  Run step() on a small subset to
                # verify we can articulate every demand (on a tiny
                # restricted state this is fast even without budget).
                tiny_state = state.restrict(
                    thing_ids=frozenset(
                        tid for tid, _ in state.things[:5]
                    )
                )
                s_unbounded = step(tiny_state, scorer=scorer_xor_off_diagonal)
                last_traj = s_unbounded.trajectory[-1]
                assert last_traj["max_articulations_per_step"] is None, (
                    "unbounded budget default should appear in trajectory"
                )
                # All demanded wedges in the tiny restricted state were
                # articulated
                assert last_traj["articulated_count"] == last_traj["demanded_count"], (
                    f"with unbounded budget, all {last_traj['demanded_count']} "
                    f"demanded should articulate; got {last_traj['articulated_count']}"
                )

                print(f"    Stage 5 + 5.5 step(): articulated {pool_growth} wedges "
                      f"in iter 1; {s2.pool.size() - s1.pool.size()} more in iter 2; "
                      f"unbounded budget on tiny restrict articulated "
                      f"{last_traj['articulated_count']}/{last_traj['demanded_count']}; "
                      f"σ-channel path exercised")

                # -- Stage 6: run_to_fixed_point() ---------------------
                # Synthetic minimal state: 3 atoms × 3 things; pool
                # closure is small enough to reach fixed-point quickly
                # and verify convergence is a genuine fixed-point.
                ax = Atom(Observable("synth_x"))
                ay = Atom(Observable("synth_y"))
                az = Atom(Observable("synth_z"))
                syn_pool = Pool().with_k(ax).with_k(ay).with_k(az)
                idx_x = syn_pool.bit_of(ax)
                idx_y = syn_pool.bit_of(ay)
                idx_z = syn_pool.bit_of(az)
                pool_size = syn_pool.size()
                # t1 fires all three; t2 fires x,y; t3 fires x,z
                def _synthetic_mask(*indices) -> np.ndarray:
                    arr = np.zeros(pool_size, dtype=bool)
                    for i in indices:
                        arr[i] = True
                    return arr
                m1 = _synthetic_mask(idx_x, idx_y, idx_z)
                m2 = _synthetic_mask(idx_x, idx_y)
                m3 = _synthetic_mask(idx_x, idx_z)
                syn_things = (
                    (ThingId("syn_t1"), Thing(id=ThingId("syn_t1"),
                                              tau_mask=m1.copy(),
                                              sigma_mask=m1.copy())),
                    (ThingId("syn_t2"), Thing(id=ThingId("syn_t2"),
                                              tau_mask=m2.copy(),
                                              sigma_mask=m2.copy())),
                    (ThingId("syn_t3"), Thing(id=ThingId("syn_t3"),
                                              tau_mask=m3.copy(),
                                              sigma_mask=m3.copy())),
                )
                syn_state = State(pool=syn_pool, things=syn_things)

                # Run to fixed point
                fixed = run_to_fixed_point(syn_state)

                # Termination reached: one more step should add nothing
                verify = step(fixed)
                assert verify.signature() == fixed.signature(), (
                    "run_to_fixed_point did not reach a true fixed point; "
                    "step() still changes state signature after"
                )
                # Articulated count on the verification step is 0
                verify_traj = verify.trajectory[-1]
                assert verify_traj["articulated_count"] == 0, (
                    f"fixed-point state should produce 0 articulations on "
                    f"next step; got {verify_traj['articulated_count']}"
                )

                # Trajectory records every iteration
                n_iters = len(fixed.trajectory) - len(syn_state.trajectory)
                assert n_iters >= 1, (
                    "run_to_fixed_point should produce at least one "
                    "trajectory entry"
                )

                # Pool has grown: at minimum x∧y (co-fire on t1,t2),
                # x∧z (co-fire on t1,t3), y∧z (co-fire on t1) are
                # articulated; possibly also x∧y∧z on t1.
                assert fixed.pool.size() > syn_pool.size(), (
                    "fixed-point pool should be larger than initial"
                )

                # Verify the three expected grade-2 wedges exist
                for a, b in [(ax, ay), (ax, az), (ay, az)]:
                    w = Wedge(a, b).normalize()
                    assert fixed.pool.bit_of(w) is not None, (
                        f"expected wedge {w.key()[:40]!r} not in fixed-point pool"
                    )

                # And the grade-3 wedge (fires only on t1)
                w3 = Wedge(ax, Wedge(ay, az)).normalize()
                assert fixed.pool.bit_of(w3) is not None, (
                    "expected grade-3 wedge not in fixed-point pool"
                )

                print(f"    Stage 6 run_to_fixed_point(): synthetic 3×3 state "
                      f"converged in {n_iters} iter(s); pool grew "
                      f"{syn_pool.size()} → {fixed.pool.size()}; "
                      f"fixed-point verified by no-op step()")

        # Pool invariant: every observable appears as an Atom K
        for k in state.pool.ks:
            assert isinstance(k, Atom), (
                f"Stage-3 initial pool should contain only Atoms, got {type(k).__name__}"
            )

        print(f"    Stage 3 extraction: {len(state.things)} things, "
              f"{state.pool.size()} atoms, {len(state.oracle_pairs)} oracle pairs")
    else:
        print("    Stage 3 extraction: no source dirs found in cwd; skipping")

    print("Stage 1–7.0 smoke test (eager-numpy internal representation): all assertions passed")
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
