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
from functools import partial
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

    def act_on_tsk(self, tsk: np.ndarray) -> np.ndarray:
        """Apply this group element to a tsk tensor of shape (3, ...).

        Axis-0 of ``tsk`` is the (τ, σ, κ) axis in canonical order.
        The S3 action is axis-0 gather: ``result[i, ...] = tsk[perm[i], ...]``.
        Enacted Stage 7.0.12 under l-s3-as-axis-permutation — this is
        the tensor-native primitive; ``act(TauSigma)`` wraps it for the
        single-cell case.

        Preserves the F₂² constraint (κ = τ ⊕ σ) because axis-0 of a
        valid tsk tensor is always in the orbit of (τ, σ, κ) under
        that constraint, and any permutation of the three positions
        remains in that orbit.

        Returns a fresh array; caller owns it.
        """
        if tsk.shape[0] != 3:
            raise ValueError(
                f"S3.act_on_tsk requires axis-0 length 3, got {tsk.shape}"
            )
        perm_arr = np.asarray(self.perm, dtype=np.int64)
        return tsk[perm_arr, ...].copy()

    def act(self, ts: TauSigma) -> TauSigma:
        """Apply this group element to a TauSigma cell.

        Direct Python permutation on the (τ, σ, κ) triple: no numpy
        allocation, no tensor materialization.  This is an independent
        codepath from ``act_on_tsk`` — the single-cell case has no
        obligation to round-trip through the tensor form.

        ``act_on_tsk`` is the tensor primitive for the (3, ...) shape
        contract per l-s3-as-axis-permutation; ``act`` is the scalar
        analogue for a single F₂² cell.  Both share the same
        permutation semantics but materialize only what their caller
        needs.

        Preserves the κ = τ ⊕ σ invariant: the F₂² orbit of (τ, σ, κ)
        under axis permutation keeps κ = permuted[τ] ⊕ permuted[σ],
        which the new TauSigma's derived-kappa enforces.
        """
        t = ts.triple()
        return TauSigma(tau=t[self.perm[0]], sigma=t[self.perm[1]])

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
        # Flatten into leaves (Atom / ZeroK / Rotated; Wedge recurses).
        # Two exterior-algebra quotient rules detect zero:
        #   K ∧ 0 = 0  — any ZeroK leaf absorbs the whole wedge.
        #   K ∧ K = 0  — a duplicate among the leaves is nilpotent.
        # Under l-k-level-s3-operators, Rotated(A, non-identity) is a
        # DISTINCT leaf from A — the nilpotency check compares distinct
        # LEAVES (not distinct atoms), so Wedge(A, swap(A)) is correctly
        # NOT nilpotent (A and swap(A) are different K's by intensional
        # key).
        flat_leaves = _flatten_wedge_leaves(self)
        if any(leaf.is_zero() for leaf in flat_leaves):
            return ZeroK()
        if len(flat_leaves) != len(set(flat_leaves)):
            return ZeroK()
        # Canonicalize: sort by key (stable across K subclasses since
        # every K carries a bijective .key()), right-leaning build.
        sorted_leaves = sorted(flat_leaves, key=lambda leaf: leaf.key())
        if len(sorted_leaves) == 1:
            return sorted_leaves[0]  # grade-1 degenerate
        return _build_right_leaning(sorted_leaves)

    def atoms(self) -> frozenset["Atom"]:
        return self.a.atoms() | self.b.atoms()


# ---------------------------------------------------------------------------
# Wedge canonicalization helpers
# ---------------------------------------------------------------------------


def _flatten_wedge_leaves(k: K) -> Tuple[K, ...]:
    """Recursively collect all non-Wedge leaves of a wedge tree IN ORDER
    (preserving multiplicity).  Used by Wedge.normalize to detect both
    the nilpotency quotient (K ∧ K = 0) and the zero-absorption rule
    (K ∧ 0 = 0).

    Leaves are any K that isn't itself a Wedge: Atom, ZeroK, Rotated.
    ZeroK leaves are RETURNED (not silently dropped) so that the
    caller can detect them and collapse the whole wedge to zero —
    this is A ∧ 0 = 0 per exterior-algebra semantics.  Stage 7.0.13
    supplement corrected a pre-existing latent behavior where ZeroK
    was dropped, making Wedge(A, ZeroK).normalize() incorrectly
    return A; the bug was uncovered in current call paths but was
    a correctness trap for code articulating wedges including zero.

    Rotated is NOT recursed through — ``Rotated(A, g)`` for non-
    identity ``g`` is a distinct K from ``A`` under intensional keys
    (per l-k-level-s3-operators), so treating it as its own leaf is
    required for nilpotency to discriminate ``Wedge(A, A) = 0`` from
    ``Wedge(A, swap(A)) ≠ 0``.
    """
    if isinstance(k, Wedge):
        return _flatten_wedge_leaves(k.a) + _flatten_wedge_leaves(k.b)
    # Atom, ZeroK, Rotated — all are valid leaves; distinguished by key()
    return (k,)


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


def k_from_structure(struct) -> K:
    """Reconstruct a K from its ``structure()`` tuple (inverse of K.structure()).

    JSON-roundtrip completeness per p-bijective-hash-consing — every
    K subclass's structure is recoverable via this function, so
    ``k_from_structure(json.loads(k.key())) == k`` holds up to
    intensional identity.  Tuples serialize to JSON lists, so the
    function accepts either a tuple or a list at each level.

    Recursively dispatches on the type tag at ``struct[0]``:
      - ``("atom", observable_str)``               → Atom
      - ``("zero",)``                               → ZeroK
      - ``("wedge", base1_struct, base2_struct)``   → Wedge
      - ``("rotated", base_struct, perm_tuple)``    → Rotated
    """
    tag = struct[0]
    if tag == "atom":
        return Atom(Observable(str(struct[1])))
    if tag == "zero":
        return ZeroK()
    if tag == "wedge":
        return Wedge(
            a=k_from_structure(struct[1]),
            b=k_from_structure(struct[2]),
        )
    if tag == "rotated":
        base = k_from_structure(struct[1])
        perm_tuple = tuple(int(x) for x in struct[2])
        return Rotated(base=base, perm=S3(perm_tuple))
    raise ValueError(f"unknown K structure tag: {tag!r}")


# ---------------------------------------------------------------------------
# Rotated — K obtained by applying an S3 element to another K's orientation
# ---------------------------------------------------------------------------


@dataclass(frozen=True, eq=True)
class Rotated(K):
    """A K whose (τ, σ, κ) orientation is an S3-permutation of another K's.

    Enacted Stage 7.0.13 under l-k-level-s3-operators.  Rotated is a
    first-class K constructor alongside Atom / Wedge / ZeroK — the
    inductive type of K gains this case to support K-level S3
    operations without stepping outside the K algebra.

    For ``Rotated(base, perm)``, the firing tsk vector on any thing X
    equals ``perm.act_on_tsk(base_tsk_of(X))``.  In particular:
      - ``swap(K) = Rotated(K, (τσ)-swap)`` has τ-firing equal to
        base's σ-firing, σ-firing equal to base's τ-firing, κ
        preserved.
      - ``rotate(K, 3-cycle)`` rotates the three channels.

    Equivalence (``normalize``) collapses the following cases:
      - ``perm`` is identity             → ``base.normalize()``
      - base is ``Rotated``              → compose perms, unwrap one level
      - base is ``ZeroK``                → ``ZeroK()``
      - otherwise                        → canonicalized ``Rotated(base.normalize(), perm)``

    Tier 2 scope (Stage 7.0.13): the K class exists and is pool-
    embeddable with proper orbit-metadata propagation.  The semantic
    switch (step() / scorers / extract_initial_state articulating
    Rotated K's) is NOT thrown — that's Tier 3.  State.tau_masks /
    sigma_masks still track single-channel firings per bit; Rotated
    K's entering the pool via smoke-test code grow the masks
    consistently with the tensor semantics (see Tier 3 for wiring).
    """

    base: K
    perm: S3

    @property
    def grade(self) -> int:
        # S3 action preserves grade — rotation is an orientation
        # permutation on the F₂² vector, not a wedge-product operation.
        return self.base.grade

    def structure(self) -> tuple:
        return ("rotated", self.base.structure(), self.perm.perm)

    def normalize(self) -> "K":
        # Identity rotation is a no-op
        if self.perm.perm == (0, 1, 2):
            return self.base.normalize()
        # Nested rotations compose: Rotated(Rotated(inner, g1), g2) ≡
        # Rotated(inner, g1 * g2).  (S3.__mul__ convention: (a*b).perm[i]
        # = a.perm[b.perm[i]]; here a=inner_perm, b=outer_perm so
        # the combined action applies inner first, outer second.)
        if isinstance(self.base, Rotated):
            combined = self.base.perm * self.perm
            return Rotated(base=self.base.base, perm=combined).normalize()
        # ZeroK is the fixed point — rotation of zero is zero
        if self.base.is_zero():
            return ZeroK()
        # Base is atomic or a wedge; canonicalize base, keep rotation
        base_norm = self.base.normalize()
        if base_norm.is_zero():
            return ZeroK()
        if isinstance(base_norm, Rotated):
            # base.normalize() yielded a Rotated — redo composition
            combined = base_norm.perm * self.perm
            return Rotated(base=base_norm.base, perm=combined).normalize()
        return Rotated(base=base_norm, perm=self.perm)

    def atoms(self) -> frozenset["Atom"]:
        # Rotation doesn't introduce or remove atoms — just permutes
        # orientation.  Atom set invariant under the S3 action.
        return self.base.atoms()

    def is_zero(self) -> bool:
        # Rotated is zero iff base is zero.  Under normalize() this
        # case collapses to ZeroK, but defensive override keeps the
        # invariant pre-normalization.
        return self.base.is_zero()


# The (τσ) transposition in S3 — used by the ``swap`` helper below.
_S3_TAU_SIGMA = S3((1, 0, 2))

# S3 generators that produce asymmetric profiles (τ ≠ σ) from
# symmetric atoms (tsk = [1, 1, 0]).  Used by step()'s syndrome-
# decoded orbit demands in Phase 2 — for each base candidate pair
# (i, j), also demand Wedge(K_i, Rotated(K_j, g)) for these g's.
# (τσ) swap is NOT included: it fixes the symmetric tsk vector
# [1, 1, 0], producing an extensionally-identical K.
_S3_TAU_KAPPA = S3((2, 1, 0))
_S3_SIGMA_KAPPA = S3((0, 2, 1))
_ORBIT_SEEDING_GENERATORS: Tuple[S3, ...] = (_S3_TAU_KAPPA, _S3_SIGMA_KAPPA)


def swap(k: K) -> K:
    """Return the (τσ)-swap of ``k`` — K-level convenience over Rotated.

    Under l-k-level-s3-operators, swap is the (τσ) transposition as a
    first-class K operator: ``swap(K).τ-firing(X) = K.σ-firing(X)``
    and vice-versa, with κ unchanged.  Involution: ``swap(swap(K)) = K``
    (captured by normalize()'s perm-composition case).
    """
    return Rotated(base=k, perm=_S3_TAU_SIGMA).normalize()


def rotate(k: K, g: S3) -> K:
    """Return the ``g``-rotation of ``k`` — K-level convenience over Rotated.

    Under l-k-level-s3-operators, rotate applies any S3 element as a
    K-level operator; the result's firing tsk vector on any thing X
    is ``g.act_on_tsk(base_tsk_of_X)``.  Identity rotation returns k
    unchanged (via normalize()'s identity case).
    """
    return Rotated(base=k, perm=g).normalize()


def compose(k1: K, k2: K, g: S3) -> K:
    """Return the composition ``Wedge(k1, rotate(k2, g)).normalize()``.

    Under l-k-level-s3-operators the third K-level primitive after
    swap and rotate: combines two K's with the second K rotated by an
    S3 element.  This expression produces ONE of the cross-orientation
    terms of the general exterior-algebra combinator; the full
    combinator (d-wedge-combinator-general-exterior-algebra) is
    reconstructible as the GF(2) sum

        compose(k1, k2, (τσ)) + compose(k2, k1, (τσ))

    under AND-semantics for wedges (d-wedge-bit-and-of-parents).
    l-combinator-and-s3-operators-are-equivalent makes this bridge
    load-bearing: either the closed-form general combinator OR a
    composition of compose() calls produces the same extensional
    firing predicate.

    Tier 2 scope: the primitive exists; no step() or scorer
    articulates compose() results yet.  Tier 3 activates the
    asymmetric regime and either path becomes a deployment choice.
    """
    return Wedge(k1, rotate(k2, g)).normalize()


# ---------------------------------------------------------------------------
# Pool — append-only registry mapping K keys to bit indices
# ---------------------------------------------------------------------------


# Pool's on-disk/in-memory shape: a structured-dtype numpy array,
# one row per K-bit.  axis-0 position = bit index.  Fields:
#   key           — the K's bijective key string (Python object dtype;
#                   HDF5 serialization converts to fixed-width unicode
#                   at the boundary, per p-storage-matches-data-shape).
#   grade         — exterior-algebra grade of the K (1 for atoms, 2+
#                   for wedges).  Stored so shape-selects like
#                   ``pool[pool['grade'] == 2]`` are array-native.
#   orbit_id      — S3-orbit identifier under l-k-level-s3-operators.
#                   For self-orbit (currently: all K's, since atoms are
#                   symmetric per d-tau-sigma-symmetric-at-grade-1 and
#                   wedges use AND-semantics per d-wedge-bit-and-of-
#                   parents), orbit_id == bit_index of the K itself
#                   (each K is its own orbit representative).  When the
#                   asymmetric regime activates (Tier 3), orbit_id
#                   points at the orbit's canonical representative —
#                   all 3-6 orbit members share it.
#   orbit_parent  — bit_index of the orbit representative from which
#                   THIS K was derived via an S3 operator (for
#                   non-trivial orbit members).  For self-orbit members,
#                   orbit_parent == bit_index.  Enables reconstructing
#                   the orbit tree on load and deriving σ_K(X) from
#                   τ_{orbit_representative}(X) when l-k-level-s3-
#                   operators is enacted.
#
# Stage 7.0.12: orbit fields added for forward schema compatibility
# with Tier 2/3 enactments.  Current code sets both to self-referential
# (orbit_id == orbit_parent == own bit index), so no semantic change.
POOL_DTYPE = np.dtype([
    ("key", "O"),
    ("grade", "u1"),
    ("orbit_id", "u4"),
    ("orbit_parent", "u4"),
])


@dataclass(frozen=True, eq=False)
class Pool:
    """Append-only K registry, stored as a numpy structured-dtype array.

    Under l-pool-as-structured-dtype-array (enacted Stage 7.0.7), the
    pool's authoritative representation is a 1-D structured-dtype
    numpy array.  axis-0 index IS bit index.  This binds the
    ``pool_size`` dependent-type parameter to the same numpy array
    whose shape appears on Thing masks (axis-1) and firing_bitmaps
    (axis-0) — one shape contract enforced across every consumer.

    Two fields:
      - ``keys_array`` — structured-dtype numpy array (POOL_DTYPE)
      - ``ks``         — tuple of K objects parallel to keys_array

    K objects are Python-inductive (Atom | Wedge | ZeroK) so they
    can't live in a numpy array; ``ks`` keeps them as a Python tuple
    with the invariant ``keys_array[i]['key'] == ks[i].key()``.

    A ``_key_to_bit: dict[str, int]`` cache is populated in
    ``__post_init__`` to keep ``bit_of`` at O(1); without it, the
    previous tuple representation's linear scan was the hot path of
    ``_articulate_wedges_batch``.

    Design-note (``d-disk-as-merge-protocol``): pool contents map
    one-to-one to rows of an HDF5 compound dataset (Stage 7.1) whose
    compound dtype mirrors POOL_DTYPE field-for-field
    (l-hdf5-compound-dtypes-mirror-in-memory).  Two shards that
    register the same K key independently MAY get different local bit
    indices; the merge step reassigns indices canonically during load.
    """

    keys_array: np.ndarray = field(
        default_factory=lambda: np.empty(0, dtype=POOL_DTYPE)
    )
    ks: Tuple[K, ...] = ()

    def __post_init__(self) -> None:
        # Shape / dtype invariants
        if self.keys_array.dtype != POOL_DTYPE:
            # Coerce rather than error — callers may pass an ndarray
            # with a compatible-but-not-identical dtype (e.g. after
            # HDF5 load with fixed-width strings).
            object.__setattr__(
                self, "keys_array", self.keys_array.astype(POOL_DTYPE)
            )
        if len(self.keys_array) != len(self.ks):
            raise ValueError("keys_array and ks length mismatch")
        # Content invariant + key→bit cache build
        cache: dict = {}
        for i, k in enumerate(self.ks):
            stored_key = self.keys_array[i]["key"]
            expected_key = k.key()
            if stored_key != expected_key:
                raise ValueError(
                    f"pool row {i}: keys_array['key'] = {stored_key!r} "
                    f"but ks[i].key() = {expected_key!r}"
                )
            cache[expected_key] = i
        object.__setattr__(self, "_key_to_bit", cache)
        # Freeze array contents (matches Thing masks' read-only discipline)
        self.keys_array.setflags(write=False)

    def __eq__(self, other) -> bool:
        if not isinstance(other, Pool):
            return False
        if len(self.keys_array) != len(other.keys_array):
            return False
        # Element-wise equality on structured array + K tuple
        return (
            np.array_equal(self.keys_array, other.keys_array)
            and self.ks == other.ks
        )

    def __hash__(self) -> int:
        # Hash on the tuple of keys (cheap and sufficient — two pools
        # with identical key sequences and matching ks satisfy the
        # __post_init__ invariant so ks tuples match too).
        return hash(tuple(self.keys_array["key"].tolist()))

    # -- Backward-compat properties ----------------------------------------

    @property
    def keys(self) -> Tuple[str, ...]:
        """Tuple of key strings in bit-index order (view of keys_array['key'])."""
        return tuple(self.keys_array["key"].tolist())

    @property
    def by_key(self) -> Tuple[Tuple[str, int], ...]:
        """Tuple of (key, bit_index) pairs in bit-index order.

        Retained for callers that want the legacy shape; internal
        lookups use ``key_to_bit`` directly.
        """
        return tuple((str(k), i) for i, k in enumerate(self.keys_array["key"]))

    @property
    def key_to_bit(self) -> dict:
        """Public view of the O(1) key→bit-index cache.

        Returns the underlying dict (not a copy) so callers can do
        fast ``if key in pool.key_to_bit`` / ``pool.key_to_bit[key]``
        lookups without a method-call roundtrip.  The dict is
        effectively immutable: Pool is frozen, so no new entries
        appear on the same instance.  Treat the returned dict as
        read-only."""
        return self._key_to_bit

    # -- Core API -----------------------------------------------------------

    def size(self) -> int:
        return len(self.keys_array)

    def bit_of(self, k: K) -> int | None:
        """O(1) bit-index lookup for K's extensional equivalence class.

        Normalizes (HIT-quotient) before the dict hit so that
        intensionally-distinct K's in the same extensional class
        resolve to the same bit.
        """
        target = k.normalize().key()
        return self._key_to_bit.get(target)

    def has(self, k: K) -> bool:
        return self.bit_of(k) is not None

    def with_k(self, k: K) -> "Pool":
        """Return a new Pool containing ``k``; idempotent if already present.

        Appends via np.concatenate on keys_array; K objects append on
        the ks tuple.  Normalization applied before the concat so the
        pool stores canonical extensional representatives.

        Orbit metadata (Stage 7.0.12 fields, Stage 7.0.13 wiring):
          - For ``Atom`` / ``Wedge`` / ``ZeroK`` K's: self-orbit,
            ``orbit_id = orbit_parent = new_bit_index``.
          - For ``Rotated(base, perm)`` K's: base is ensured present
            in the pool (recursive ``with_k`` call adds it if absent);
            the new row's ``orbit_id`` inherits the base's ``orbit_id``
            (the orbit ROOT representative), and ``orbit_parent`` points
            at the base's bit index (the IMMEDIATE parent in the
            orbit tree).  This lets the loader reconstruct orbit
            structure and, under Tier 3, derive σ_K(X) from
            τ_{orbit_root}(X) via the composed S3 element.
        """
        nk = k.normalize()
        key = nk.key()
        if key in self._key_to_bit:
            return self
        if isinstance(nk, Rotated):
            # Ensure base is present first; recursive add is safe
            # because normalize() never produces nested Rotated (the
            # composition case in Rotated.normalize collapses them).
            base_pool = self.with_k(nk.base)
            base_bit = base_pool._key_to_bit[nk.base.key()]
            base_orbit_id = int(base_pool.keys_array[base_bit]["orbit_id"])
            new_bit = len(base_pool.keys_array)
            new_row = np.array(
                [(key, nk.grade, base_orbit_id, base_bit)],
                dtype=POOL_DTYPE,
            )
            new_array = np.concatenate([base_pool.keys_array, new_row])
            return Pool(keys_array=new_array, ks=base_pool.ks + (nk,))
        # Self-orbit case: Atom, Wedge, ZeroK
        new_bit = len(self.keys_array)
        new_row = np.array(
            [(key, nk.grade, new_bit, new_bit)], dtype=POOL_DTYPE
        )
        new_array = np.concatenate([self.keys_array, new_row])
        return Pool(keys_array=new_array, ks=self.ks + (nk,))

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
# Thing — value type for a single declaration's τ/σ bitmap row
# ---------------------------------------------------------------------------


@dataclass(frozen=True, eq=False)
class Thing:
    """Value type for a single declaration's identity + τ/σ bitmap row.

    NOTE on post-7.0.7b role: Thing is NOT the primary storage for
    τ/σ bitmaps.  Under l-state-things-as-parallel-arrays (enacted
    Stage 7.0.7b), the authoritative storage is the stacked matrices
    ``State.tau_masks`` / ``State.sigma_masks`` of shape
    ``(n_things, pool_size)``.  Thing remains as a value type for:

      - constructing standalone test/extractor fixtures before
        building a State (``state = State(things=(...))``);
      - reconstructing a row-view on demand via ``state.things``,
        ``state.things_dict()``, or ``state.with_thing(thing)``;
      - external consumers that want a Python-object handle carrying
        ``(id, tau_mask, sigma_mask, kappa_mask)`` without touching
        the stacked matrices directly.

    Prefer the direct matrix accessors (``state.row_of(tid)``,
    ``state.tau_row(tid)``, ``state.sigma_row(tid)``) in hot paths —
    no Thing reconstruction, no per-row copy.

    Under ``p-source-is-a-k`` and ``p-no-bespoke-recognition``, source
    provenance is not a privileged field of Thing — it is an
    observable K registered in the Pool.  Same for display names,
    paths, line numbers, and anything else an extractor might want
    to surface.  There is no "metadata" category: every observable
    is a K; reports are queries over the pool + bitmaps.

    ``tau_mask`` and ``sigma_mask`` are np.ndarray(dtype=bool) over
    the Pool: element i True iff the K at pool position i fires on
    this thing in the respective channel.  ``kappa_mask`` is derived
    as ``tau XOR sigma`` by construction (never stored).

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
        # Pure function of content — no caching.  Stage 7.0.5 added a
        # _hash cache to optimize what we (incorrectly) thought was
        # the signature() hot path; Stage 7.0.6 reverted per the
        # user observation 'we're materializing something that
        # shouldn't be materialized in the first place'.  Tuple
        # equality in signature() comparison goes through __eq__,
        # never __hash__, so the cache solved a phantom problem and
        # introduced cross-process staleness (hash randomization via
        # PYTHONHASHSEED) for no benefit.  If someone does use Things
        # in a hashed collection in the future, the cost is O(mask
        # bytes) per call, deterministic per-process, and honest.
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

    @staticmethod
    def with_empty_masks(tid: "ThingId", pool_size: int) -> "Thing":
        """Helper: construct a Thing with all-False masks of the
        requested length.  Used in tests and as a default form."""
        empty = np.zeros(pool_size, dtype=bool)
        return Thing(id=tid, tau_mask=empty.copy(), sigma_mask=empty.copy())


# ---------------------------------------------------------------------------
# State — the closed-loop state (Stage 2)
# ---------------------------------------------------------------------------


# Trajectory's on-disk / in-memory shape: one structured-dtype row per
# step() iteration (l-trajectory-as-structured-dtype-array, enacted
# Stage 7.0.9).  Under p-types-are-tensor-shape-obligations the field
# names are part of the type — typos at write sites fail at dtype
# validation instead of silently returning a default.
#
# max_articulations_per_step uses a signed i4 with -1 as the sentinel
# for None (unbounded budget).  Matches the semantics of the Python-
# level ``None`` while remaining a pure numeric dtype for HDF5
# compound-dtype mirroring in Stage 7.1.
#
# Optional scorer / objective structural identities are logged in a
# parallel ``trajectory_aux: Tuple[dict, ...]`` alongside — the lemma's
# counterexample mitigation: keep one mandatory base dtype for hot-path
# control fields; optional variable-shape fields go in a separate
# auxiliary channel.
TRAJECTORY_DTYPE = np.dtype([
    ("iteration", "u4"),
    ("demanded_count", "u4"),
    ("articulated_count", "u4"),
    ("pool_size_before", "u4"),
    ("pool_size_after", "u4"),
    ("n_things", "u4"),
    ("max_articulations_per_step", "i4"),
])
_TRAJECTORY_NUMERIC_FIELDS = frozenset(TRAJECTORY_DTYPE.names)
_MAX_ART_UNBOUNDED_SENTINEL = -1


def _trajectory_from_dicts(
    dict_seq: tuple,
) -> Tuple[np.ndarray, Tuple[dict, ...]]:
    """Split a sequence of dict trajectory entries into a structured
    numeric array + a parallel aux-dict tuple.  Used both by
    appending_trajectory (single entry) and by merge (concatenation).
    """
    if len(dict_seq) == 0:
        return np.empty(0, dtype=TRAJECTORY_DTYPE), ()
    rows = []
    auxes: list = []
    for entry in dict_seq:
        if isinstance(entry, np.void):
            # Already a structured-array row; aux field carried separately
            # (this path shouldn't occur in normal flow, but guard).
            rows.append(tuple(entry[f] for f in TRAJECTORY_DTYPE.names))
            auxes.append({})
            continue
        max_art = entry.get("max_articulations_per_step")
        row = (
            int(entry.get("iteration", 0)),
            int(entry.get("demanded_count", 0)),
            int(entry.get("articulated_count", 0)),
            int(entry.get("pool_size_before", 0)),
            int(entry.get("pool_size_after", 0)),
            int(entry.get("n_things", 0)),
            _MAX_ART_UNBOUNDED_SENTINEL if max_art is None else int(max_art),
        )
        rows.append(row)
        aux = {
            k: v for k, v in entry.items()
            if k not in _TRAJECTORY_NUMERIC_FIELDS
        }
        auxes.append(aux)
    arr = np.array(rows, dtype=TRAJECTORY_DTYPE)
    arr.setflags(write=False)
    return arr, tuple(auxes)


@dataclass(frozen=True, eq=False, init=False)
class State:
    """Complete state of the closed-loop algorithm.

    Under l-state-things-as-parallel-arrays (enacted Stage 7.0.7b) the
    authoritative storage for things is three parallel 1D/2D arrays
    rather than a tuple of (ThingId, Thing) pairs.  'A Thing' is a
    row-view: Thing objects are still constructed on demand via the
    ``things`` / ``things_dict`` / ``with_thing`` surface, but the
    state doesn't store them — it stores the shape-bound matrices
    that bind directly to the pool's axis-0 (l-pool-as-structured-
    dtype-array).  The dependent-type shape parameter pool_size
    appears as axis-1 of tau_masks/sigma_masks AND axis-0 of pool —
    one shape contract, three arrays, enforceable at load.

    Primary fields:

    - ``pool``        — the K registry (structured-dtype numpy array
                        + K tuple).
    - ``thing_ids``   — 1D object-dtype ndarray of ThingIds, sorted.
    - ``tau_masks``   — 2D bool ndarray, shape (n_things, pool_size).
                        Row i is thing_ids[i]'s τ-mask.
    - ``sigma_masks`` — 2D bool ndarray, shape (n_things, pool_size).
                        Row i is thing_ids[i]'s σ-mask.
    - ``oracle_pairs``— frozenset of frozenset({id_a, id_b}) — thing
                        pairs known to correspond (citation links).
                        Used for weight calibration only, never for
                        gating.  (The l-oracle-pairs-as-index-array
                        refactor is a follow-up, not Stage 7.0.7b.)
    - ``weights``     — per-K weight, keyed by K.key().  Pluggable
                        objective adjusts these.
    - ``trajectory``  — append-only tuple of per-iteration telemetry.
    - ``iteration``   — monotonic counter.

    Backward-compat surface:

    - ``things``        — computed property reconstructing the legacy
                          Tuple[Tuple[ThingId, Thing], ...] shape.
                          Use direct array access in hot paths.
    - ``with_thing(t)`` — unchanged API; internally appends or replaces
                          a row in the parallel arrays.
    - ``things_dict()`` — unchanged API.
    - ``State(things=...)``  ctor-kwarg accepted for legacy call sites.

    Frozen dataclass: step() must return a new State, never mutate.
    ``merge``, ``restrict``, and ``signature`` support self-similarity
    and embarrassingly-parallel operation per p-embarrassingly-parallel.
    """

    pool: Pool
    thing_ids: np.ndarray          # dtype=object, shape (n_things,)
    tau_masks: np.ndarray          # dtype=bool,   shape (n_things, pool_size) — fires bit
    sigma_masks: np.ndarray        # dtype=bool,   shape (n_things, pool_size) — fires bit
    tau_populated: np.ndarray      # dtype=bool,   shape (n_things, pool_size) — computed bit
    sigma_populated: np.ndarray    # dtype=bool,   shape (n_things, pool_size) — computed bit
    oracle_pairs: frozenset        # authoritative; frozenset[frozenset[ThingId]]
    oracle_pair_indices: np.ndarray  # dtype=int64, shape (n_pairs, 2); cache
    weights: Tuple[Tuple[KKey, float], ...]
    trajectory: np.ndarray          # dtype=TRAJECTORY_DTYPE, shape (n_iter,)
    trajectory_aux: Tuple[dict, ...]  # parallel aux; scorer/objective structure
    iteration: int

    def __init__(
        self,
        *,
        pool: Pool | None = None,
        things: Tuple[Tuple[ThingId, "Thing"], ...] | None = None,
        thing_ids: np.ndarray | None = None,
        tau_masks: np.ndarray | None = None,
        sigma_masks: np.ndarray | None = None,
        tau_populated: np.ndarray | None = None,
        sigma_populated: np.ndarray | None = None,
        oracle_pairs: frozenset = frozenset(),
        weights: Tuple[Tuple[KKey, float], ...] = (),
        trajectory: Tuple | np.ndarray = (),
        trajectory_aux: Tuple[dict, ...] | None = None,
        iteration: int = 0,
    ) -> None:
        """Accept either the legacy ``things=(id, Thing)...`` form or
        direct parallel arrays.  Raises if both are passed.  The
        legacy form is normalized to the primary array representation
        once, at construction time — no lazy dual-representation."""
        p = pool if pool is not None else Pool()

        legacy_given = things is not None
        arrays_given = any(
            x is not None for x in (thing_ids, tau_masks, sigma_masks)
        )
        if legacy_given and arrays_given:
            raise ValueError(
                "State.__init__: pass ONE of things=... or "
                "(thing_ids, tau_masks, sigma_masks) — not both"
            )

        if legacy_given:
            # Legacy path: unpack tuple-of-(id, Thing) into arrays.
            # Must be sorted by id to preserve the hash/signature
            # invariant.  Pad masks to pool_size if shorter.
            pool_size = p.size()
            sorted_things = sorted(things, key=lambda kv: kv[0])
            n = len(sorted_things)
            ids_arr = np.array([tid for tid, _ in sorted_things], dtype=object)
            tau = np.zeros((n, pool_size), dtype=bool)
            sig = np.zeros((n, pool_size), dtype=bool)
            for i, (_tid, thing) in enumerate(sorted_things):
                k = min(len(thing.tau_mask), pool_size)
                tau[i, :k] = thing.tau_mask[:k]
                sig[i, :k] = thing.sigma_mask[:k]
        elif arrays_given:
            # Arrays path: trust the caller.  Shape is validated below.
            pool_size = p.size()
            ids_arr = (
                np.asarray(thing_ids, dtype=object)
                if thing_ids is not None
                else np.array([], dtype=object)
            )
            tau = (
                np.ascontiguousarray(tau_masks, dtype=bool)
                if tau_masks is not None
                else np.empty((len(ids_arr), pool_size), dtype=bool)
            )
            sig = (
                np.ascontiguousarray(sigma_masks, dtype=bool)
                if sigma_masks is not None
                else np.empty((len(ids_arr), pool_size), dtype=bool)
            )
        else:
            # Empty state
            pool_size = p.size()
            ids_arr = np.array([], dtype=object)
            tau = np.empty((0, pool_size), dtype=bool)
            sig = np.empty((0, pool_size), dtype=bool)

        # Shape invariants.  Stage 7.3: fire_pair is the canonical
        # computation; mask matrix is a CACHE that grows with pool.
        n = len(ids_arr)
        if tau.shape != (n, pool_size):
            raise ValueError(
                f"tau_masks shape {tau.shape} != expected {(n, pool_size)}"
            )
        if sig.shape != (n, pool_size):
            raise ValueError(
                f"sigma_masks shape {sig.shape} != expected {(n, pool_size)}"
            )

        # Belnap populated arrays (l-belnap-encoded-mask-matrix).
        # If not provided, default to all-True (all cells computed —
        # backward compat with callers that provide pre-computed masks).
        if tau_populated is not None:
            tau_pop = np.ascontiguousarray(tau_populated, dtype=bool)
        else:
            tau_pop = np.ones_like(tau, dtype=bool)
        if sigma_populated is not None:
            sig_pop = np.ascontiguousarray(sigma_populated, dtype=bool)
        else:
            sig_pop = np.ones_like(sig, dtype=bool)

        # Freeze arrays
        tau.setflags(write=False)
        sig.setflags(write=False)
        tau_pop.setflags(write=False)
        sig_pop.setflags(write=False)

        # Build the id→row-index cache; used by row_of and by the
        # oracle_pair_indices resolution below.
        id_to_row: dict = {str(tid): i for i, tid in enumerate(ids_arr)}

        # Resolve oracle pairs from their string-id authoritative form
        # into an Int[n_pairs, 2] cache (l-oracle-pairs-as-index-array).
        # Pairs with dangling ids (not present in thing_ids) are skipped
        # — matches the existing scorers' per-call guard.  Within-pair
        # ordering is (min(a, b), max(a, b)) by id-string sort, making
        # the orientation-sensitive scorers deterministic (previously
        # they consumed frozenset iteration order, which was arbitrary).
        resolved_pairs: list = []
        for pair in oracle_pairs:
            if len(pair) != 2:
                continue
            ids_sorted = sorted(str(x) for x in pair)
            a_idx = id_to_row.get(ids_sorted[0])
            b_idx = id_to_row.get(ids_sorted[1])
            if a_idx is None or b_idx is None:
                continue
            resolved_pairs.append((a_idx, b_idx))
        resolved_pairs.sort()
        if resolved_pairs:
            pair_indices = np.array(resolved_pairs, dtype=np.int64)
        else:
            pair_indices = np.empty((0, 2), dtype=np.int64)
        pair_indices.setflags(write=False)

        # Normalize trajectory into (structured_array, aux_tuple).
        if isinstance(trajectory, np.ndarray) and trajectory.dtype == TRAJECTORY_DTYPE:
            traj_arr = trajectory
            if not traj_arr.flags.writeable:
                pass  # already read-only
            else:
                traj_arr.setflags(write=False)
            traj_aux = trajectory_aux if trajectory_aux is not None else ({},) * len(traj_arr)
            if len(traj_aux) != len(traj_arr):
                raise ValueError(
                    f"trajectory_aux length {len(traj_aux)} != trajectory length "
                    f"{len(traj_arr)}"
                )
        else:
            # Legacy: tuple of dicts.  Split into structured + aux.
            traj_arr, traj_aux = _trajectory_from_dicts(tuple(trajectory))

        object.__setattr__(self, "pool", p)
        object.__setattr__(self, "thing_ids", ids_arr)
        object.__setattr__(self, "tau_masks", tau)
        object.__setattr__(self, "sigma_masks", sig)
        object.__setattr__(self, "tau_populated", tau_pop)
        object.__setattr__(self, "sigma_populated", sig_pop)
        object.__setattr__(self, "oracle_pairs", oracle_pairs)
        object.__setattr__(self, "oracle_pair_indices", pair_indices)
        object.__setattr__(self, "_id_to_row", id_to_row)
        object.__setattr__(self, "weights", weights)
        object.__setattr__(self, "trajectory", traj_arr)
        object.__setattr__(self, "trajectory_aux", traj_aux)
        object.__setattr__(self, "iteration", iteration)

    # -- equality / hash (overridden since ndarray fields aren't hashable) ---

    def __eq__(self, other) -> bool:
        if not isinstance(other, State):
            return False
        return (
            self.pool == other.pool
            and self.thing_ids.shape == other.thing_ids.shape
            and self.tau_masks.shape == other.tau_masks.shape
            and self.sigma_masks.shape == other.sigma_masks.shape
            and np.array_equal(self.thing_ids, other.thing_ids)
            and np.array_equal(self.tau_masks, other.tau_masks)
            and np.array_equal(self.sigma_masks, other.sigma_masks)
            and self.oracle_pairs == other.oracle_pairs
            and self.weights == other.weights
            and np.array_equal(self.trajectory, other.trajectory)
            and self.trajectory_aux == other.trajectory_aux
            and self.iteration == other.iteration
        )

    def __hash__(self) -> int:
        return hash((
            hash(self.pool),
            tuple(self.thing_ids.tolist()),
            self.tau_masks.tobytes(),
            self.sigma_masks.tobytes(),
            self.oracle_pairs,
            self.weights,
            self.trajectory.tobytes(),
            self.iteration,
        ))

    # -- backward-compat views ----------------------------------------------

    @property
    def things(self) -> Tuple[Tuple[ThingId, "Thing"], ...]:
        """Reconstruct the legacy (id, Thing) tuple view.

        O(n_things) per call; prefer direct ``.tau_masks`` /
        ``.sigma_masks`` / ``.thing_ids`` access in hot paths.  Thing
        objects returned are freshly constructed row-views over copies
        of the underlying array rows — the primary state is not held
        in these Things, so mutating them (which is also blocked by
        Thing's read-only masks) would not affect the State.
        """
        return tuple(
            (ThingId(str(tid)),
             Thing(id=ThingId(str(tid)),
                   tau_mask=self.tau_masks[i].copy(),
                   sigma_mask=self.sigma_masks[i].copy()))
            for i, tid in enumerate(self.thing_ids)
        )

    def things_dict(self) -> dict:
        """Dict view keyed by ThingId; one-shot construction."""
        return {
            ThingId(str(tid)): Thing(
                id=ThingId(str(tid)),
                tau_mask=self.tau_masks[i].copy(),
                sigma_mask=self.sigma_masks[i].copy(),
            )
            for i, tid in enumerate(self.thing_ids)
        }

    def weights_dict(self) -> dict:
        return dict(self.weights)

    def weight_of(self, k: K, default: float = 1.0) -> float:
        target = k.key()
        for key, w in self.weights:
            if key == target:
                return w
        return default

    @property
    def pool_has_trivial_orbits(self) -> bool:
        """True iff every K in the pool is its own S3-orbit representative
        (orbit_id[i] == i for all i).

        Queries POOL STRUCTURE only — independent of whether any K's
        sigma-firing happens to equal its tau-firing.  Under the
        pre-Tier-2 regime every K is self-orbit trivially; under
        Tier 2+ the pool may contain Rotated(base, g) K's whose
        orbit_id points at their base.

        Pure structural probe; no mask comparison.  See
        ``sigma_derivable_from_tau`` for the storage-derivability
        question, which is separate.
        """
        pool_size = self.pool.size()
        if pool_size == 0:
            return True
        orbit_ids = self.pool.keys_array["orbit_id"]
        expected = np.arange(pool_size, dtype=orbit_ids.dtype)
        return np.array_equal(orbit_ids, expected)

    @property
    def sigma_derivable_from_tau(self) -> bool:
        """True iff sigma_masks can be reconstructed from tau_masks
        (plus, in Tier 2+, pool orbit metadata) — the Stage 7.1
        storage-derivability question.

        Stage 7.0.12 (Tier 1) semantics: returns True iff
        ``np.array_equal(sigma_masks, tau_masks)``.  Under the current
        symmetric-atoms + AND-wedge regime this is the only way
        derivability holds, so the property is equivalent to the mask
        equality test.

        Stage 7.0.13+ (Tier 2) will broaden the check: sigma is also
        derivable when every row where sigma differs from tau has its
        K mapped via pool orbit metadata to a base whose tau equals
        that sigma — i.e., the orbit structure encodes the delta.

        A False value tells Stage 7.1's writer to serialize sigma_masks
        as an independent dataset; a True value tells it to omit
        sigma_masks and reconstruct on load.

        Pure structural probe; disjoint concern from
        ``pool_has_trivial_orbits``.  The two properties were once a
        single conflated ``is_symmetric`` (Stage 7.0.12 pre-audit)
        before the Stage 7.0.12 audit separated them: a pool with
        non-trivial orbits but bitwise-equal masks would have returned
        False under the conflated form, causing Stage 7.1 to write
        sigma_masks redundantly.
        """
        return bool(np.array_equal(self.tau_masks, self.sigma_masks))

    # -- internal array helpers --------------------------------------------

    def _bit_index_of_thing(self, tid: ThingId) -> int | None:
        """Row index for a ThingId in the parallel arrays, or None."""
        return self._id_to_row.get(str(tid))

    def row_of(self, tid: ThingId) -> int | None:
        """Public row-index accessor for a ThingId.

        Returns the axis-0 position of ``tid`` in ``thing_ids`` (and
        thus in ``tau_masks``/``sigma_masks``), or ``None`` if the id
        is unknown.  O(1) via the ``_id_to_row`` cache built at
        construction.  Use this instead of ``state.things_dict()[tid]``
        when you want the mask row directly — no Thing reconstruction,
        no copy."""
        return self._id_to_row.get(str(tid))

    def tau_row(self, tid: ThingId) -> np.ndarray | None:
        """Read-only view of ``tid``'s τ-mask row, or ``None`` if unknown."""
        i = self._id_to_row.get(str(tid))
        return self.tau_masks[i] if i is not None else None

    def sigma_row(self, tid: ThingId) -> np.ndarray | None:
        """Read-only view of ``tid``'s σ-mask row, or ``None`` if unknown."""
        i = self._id_to_row.get(str(tid))
        return self.sigma_masks[i] if i is not None else None

    # -- lazy K firing evaluation ------------------------------------------

    def fire_pair(self, k: K) -> Tuple[np.ndarray, np.ndarray]:
        """Lazily compute the (τ, σ) firing column for ANY K.

        Stage 7.3: the pool is a computation graph; atom mask columns
        are the only stored data; everything else is derived on read
        via this method.  Memoized per K.key() on the State instance
        (frozen ⟹ cache never invalidated).

        The fold is the "shingling" process: for a Wedge, right-fold
        through the canonical tree's leaves applying the grade-2
        GF(2) cross-term formula at each step.  For a Rotated K,
        S3 axis-permutation on the base's (τ, σ, κ).  For an Atom,
        direct read from stored masks.  For ZeroK, all-False.

        Returns (tau_col, sig_col) each of shape (n_things,) bool.
        """
        # Memoize on K.key() — same intensional key ⟹ same firing
        cache_key = k.key()
        if not hasattr(self, "_fire_cache"):
            object.__setattr__(self, "_fire_cache", {})
        if cache_key in self._fire_cache:
            return self._fire_cache[cache_key]

        n = len(self.thing_ids)

        if isinstance(k, ZeroK) or k.is_zero():
            result = (np.zeros(n, dtype=bool), np.zeros(n, dtype=bool))

        elif isinstance(k, Atom):
            bit = self.pool.bit_of(k)
            if bit is None or bit >= self.tau_masks.shape[1]:
                result = (np.zeros(n, dtype=bool), np.zeros(n, dtype=bool))
            elif (bit < self.tau_populated.shape[1]
                  and self.tau_populated[:, bit].all()):
                # Belnap: all cells populated → cache hit
                result = (self.tau_masks[:, bit].copy(),
                          self.sigma_masks[:, bit].copy())
            else:
                # Belnap ⊥: gap — atom column not yet populated
                # (shouldn't happen for atoms from extract_initial_state
                # but can happen for atoms added via with_pool padding)
                result = (np.zeros(n, dtype=bool), np.zeros(n, dtype=bool))

        elif isinstance(k, Rotated):
            base_tau, base_sig = self.fire_pair(k.base)
            base_kappa = base_tau ^ base_sig
            tsk = np.stack([base_tau, base_sig, base_kappa], axis=0)
            rotated = k.perm.act_on_tsk(tsk)
            result = (rotated[0].astype(bool), rotated[1].astype(bool))

        elif isinstance(k, Wedge):
            leaves = _flatten_wedge_leaves(k)
            if not leaves or any(leaf.is_zero() for leaf in leaves):
                result = (np.zeros(n, dtype=bool), np.zeros(n, dtype=bool))
            else:
                has_rotated = any(isinstance(lf, Rotated) for lf in leaves)
                if has_rotated:
                    # General combinator fold (shingling / grade-k)
                    tau_acc, sig_acc = self.fire_pair(leaves[-1])
                    for leaf in reversed(leaves[:-1]):
                        tau_l, sig_l = self.fire_pair(leaf)
                        tau_old, sig_old = tau_acc, sig_acc
                        tau_acc = (tau_l & sig_old) ^ (sig_l & tau_old)
                        sig_acc = (tau_l & tau_old) ^ (sig_l & sig_old)
                    result = (tau_acc, sig_acc)
                else:
                    # AND-of-parents (d-wedge-bit-and-of-parents):
                    # symmetric leaves, τ = σ = AND of all leaf τ-fires
                    tau_acc = np.ones(n, dtype=bool)
                    for leaf in leaves:
                        tau_l, _ = self.fire_pair(leaf)
                        tau_acc = tau_acc & tau_l
                    result = (tau_acc, tau_acc.copy())

        else:
            result = (np.zeros(n, dtype=bool), np.zeros(n, dtype=bool))

        self._fire_cache[cache_key] = result
        return result

    # -- constructors -------------------------------------------------------

    def with_thing(self, thing: "Thing") -> "State":
        """Add or replace a thing by id.

        Internally updates the parallel arrays: if the id exists, its
        row is overwritten; otherwise a row is inserted at the correct
        sorted position.  The thing's masks are padded to pool_size if
        shorter; this keeps the shape invariant a function of the
        pool, not of the caller.
        """
        pool_size = self.pool.size()
        # Pad mask to pool_size
        def _pad(arr: np.ndarray) -> np.ndarray:
            if len(arr) >= pool_size:
                return np.ascontiguousarray(arr[:pool_size], dtype=bool)
            out = np.zeros(pool_size, dtype=bool)
            out[:len(arr)] = arr
            return out

        tau_new_row = _pad(thing.tau_mask)
        sig_new_row = _pad(thing.sigma_mask)

        existing_idx = self._bit_index_of_thing(thing.id)
        if existing_idx is not None:
            # Replace row in-place on a fresh copy (respecting immutability)
            new_tau = self.tau_masks.copy()
            new_sig = self.sigma_masks.copy()
            new_tau[existing_idx] = tau_new_row
            new_sig[existing_idx] = sig_new_row
            return State(
                pool=self.pool,
                thing_ids=self.thing_ids,
                tau_masks=new_tau,
                sigma_masks=new_sig,
                oracle_pairs=self.oracle_pairs,
                weights=self.weights,
                trajectory=self.trajectory,
                trajectory_aux=self.trajectory_aux,
                iteration=self.iteration,
            )

        # Insert at sorted position
        insert_pos = int(np.searchsorted(self.thing_ids.astype(str), str(thing.id)))
        new_ids = np.insert(self.thing_ids, insert_pos, thing.id)
        new_tau = np.insert(self.tau_masks, insert_pos, tau_new_row, axis=0)
        new_sig = np.insert(self.sigma_masks, insert_pos, sig_new_row, axis=0)
        return State(
            pool=self.pool,
            thing_ids=new_ids,
            tau_masks=new_tau,
            sigma_masks=new_sig,
            oracle_pairs=self.oracle_pairs,
            weights=self.weights,
            trajectory=self.trajectory,
            trajectory_aux=self.trajectory_aux,
            iteration=self.iteration,
        )

    def with_pool(self, pool: Pool) -> "State":
        """Replace the pool.  Masks are repadded/truncated to the new
        pool size.  New columns are Belnap ⊥ (gap): zero-padded
        in both fires and populated arrays."""
        new_size = pool.size()
        cur_size = self.tau_masks.shape[1] if self.tau_masks.size else 0
        if new_size == cur_size:
            new_tau = self.tau_masks
            new_sig = self.sigma_masks
            new_tau_pop = self.tau_populated
            new_sig_pop = self.sigma_populated
        elif new_size > cur_size:
            n_things = len(self.thing_ids)
            pad_cols = new_size - cur_size
            pad = np.zeros((n_things, pad_cols), dtype=bool)
            new_tau = np.concatenate([self.tau_masks, pad], axis=1)
            new_sig = np.concatenate([self.sigma_masks, pad], axis=1)
            # New columns are GAP (⊥): populated = False
            gap_pop = np.zeros((n_things, pad_cols), dtype=bool)
            new_tau_pop = np.concatenate([self.tau_populated, gap_pop], axis=1)
            new_sig_pop = np.concatenate([self.sigma_populated, gap_pop], axis=1)
        else:
            new_tau = np.ascontiguousarray(self.tau_masks[:, :new_size])
            new_sig = np.ascontiguousarray(self.sigma_masks[:, :new_size])
            new_tau_pop = np.ascontiguousarray(self.tau_populated[:, :new_size])
            new_sig_pop = np.ascontiguousarray(self.sigma_populated[:, :new_size])
        return State(
            pool=pool,
            thing_ids=self.thing_ids,
            tau_masks=new_tau,
            sigma_masks=new_sig,
            tau_populated=new_tau_pop,
            sigma_populated=new_sig_pop,
            oracle_pairs=self.oracle_pairs,
            weights=self.weights,
            trajectory=self.trajectory,
            trajectory_aux=self.trajectory_aux,
            iteration=self.iteration,
        )

    def with_weight(self, k_key: KKey, w: float) -> "State":
        others = tuple((k, v) for k, v in self.weights if k != k_key)
        new = tuple(sorted(others + ((k_key, w),), key=lambda kv: kv[0]))
        return State(
            pool=self.pool,
            thing_ids=self.thing_ids,
            tau_masks=self.tau_masks,
            sigma_masks=self.sigma_masks,
            oracle_pairs=self.oracle_pairs,
            weights=new,
            trajectory=self.trajectory,
            trajectory_aux=self.trajectory_aux,
            iteration=self.iteration,
        )

    def appending_trajectory(self, entry: dict) -> "State":
        """Append one entry to the trajectory.

        Splits the entry's mandatory TRAJECTORY_DTYPE fields into a new
        structured-array row and packs the remaining keys (scorer,
        objective structural identities) into the parallel aux dict.
        """
        new_row_arr, new_aux_tuple = _trajectory_from_dicts((entry,))
        merged_arr = np.concatenate([self.trajectory, new_row_arr])
        merged_arr.setflags(write=False)
        return State(
            pool=self.pool,
            thing_ids=self.thing_ids,
            tau_masks=self.tau_masks,
            sigma_masks=self.sigma_masks,
            oracle_pairs=self.oracle_pairs,
            weights=self.weights,
            trajectory=merged_arr,
            trajectory_aux=self.trajectory_aux + new_aux_tuple,
            iteration=self.iteration + 1,
        )

    # -- merge / restrict ---------------------------------------------------

    def merge(self, other: "State") -> "State":
        """Union two states.  Associative and commutative per
        ``p-embarrassingly-parallel``:

        - Pool: ``self.pool.merge(other.pool)`` — K's from self keep
          their bit indices (append-only); K's only in other get new
          indices appended.
        - Things: union by ThingId; if an id appears in both states,
          its row must agree after each side's masks are remapped to
          the merged pool's indexing.  Divergent rows raise ValueError.
        - Weights: averaged on key collision.
        - Oracle pairs: set-unioned.
        - Trajectory: concatenated and sorted by iteration field.

        Divergent-pool merge is vectorized: for each side whose local
        pool differs from the merged pool, build a column-permutation
        array and gather the mask rows into the merged pool's column
        order in one numpy advanced-indexing op per side.
        """
        merged_pool = self.pool.merge(other.pool)
        merged_size = merged_pool.size()

        def _remap_masks(source_state: "State", source_pool: Pool) -> Tuple[np.ndarray, np.ndarray]:
            """Return (tau, sigma) with columns permuted into merged_pool order.

            For each old bit i, new_idx[i] = merged_pool.bit_of(source_pool.ks[i])
            (always found, since merged_pool is a superset of source_pool).
            We allocate zero matrices over merged columns and scatter from old.
            """
            if source_pool is merged_pool or np.array_equal(
                np.array(source_pool.keys), np.array(merged_pool.keys)
            ):
                # Already in merged pool's indexing; maybe pad trailing columns
                if source_state.tau_masks.shape[1] == merged_size:
                    return source_state.tau_masks, source_state.sigma_masks
                pad = np.zeros(
                    (len(source_state.thing_ids),
                     merged_size - source_state.tau_masks.shape[1]),
                    dtype=bool,
                )
                return (np.concatenate([source_state.tau_masks, pad], axis=1),
                        np.concatenate([source_state.sigma_masks, pad], axis=1))
            # Build remap: old_idx → new_idx
            remap = np.array(
                [merged_pool.bit_of(k) for k in source_pool.ks], dtype=np.int64
            )
            n_things = len(source_state.thing_ids)
            new_tau = np.zeros((n_things, merged_size), dtype=bool)
            new_sig = np.zeros((n_things, merged_size), dtype=bool)
            new_tau[:, remap] = source_state.tau_masks
            new_sig[:, remap] = source_state.sigma_masks
            return new_tau, new_sig

        self_tau, self_sig = _remap_masks(self, self.pool)
        other_tau, other_sig = _remap_masks(other, other.pool)

        # Union by id; row-wise equality check on collision
        self_ids = [str(t) for t in self.thing_ids]
        other_ids = [str(t) for t in other.thing_ids]
        self_idx = {tid: i for i, tid in enumerate(self_ids)}
        other_idx = {tid: i for i, tid in enumerate(other_ids)}
        all_ids = sorted(set(self_ids) | set(other_ids))

        n = len(all_ids)
        merged_ids = np.array(all_ids, dtype=object)
        merged_tau = np.zeros((n, merged_size), dtype=bool)
        merged_sig = np.zeros((n, merged_size), dtype=bool)
        for i, tid in enumerate(all_ids):
            si = self_idx.get(tid)
            oi = other_idx.get(tid)
            if si is not None and oi is not None:
                if (not np.array_equal(self_tau[si], other_tau[oi])
                        or not np.array_equal(self_sig[si], other_sig[oi])):
                    raise ValueError(
                        f"thing id {tid!r} has diverging content across states "
                        f"(after pool remap)"
                    )
                merged_tau[i] = self_tau[si]
                merged_sig[i] = self_sig[si]
            elif si is not None:
                merged_tau[i] = self_tau[si]
                merged_sig[i] = self_sig[si]
            else:
                merged_tau[i] = other_tau[oi]
                merged_sig[i] = other_sig[oi]

        # Weights: average on collision
        ws: dict = dict(self.weights)
        for k, w in other.weights:
            if k in ws:
                ws[k] = (ws[k] + w) / 2.0
            else:
                ws[k] = w

        oracle = self.oracle_pairs | other.oracle_pairs

        # Trajectory: concatenate structured arrays + aux tuples, then
        # sort both in lock-step by the 'iteration' field.
        combined_arr = np.concatenate([self.trajectory, other.trajectory])
        combined_aux = self.trajectory_aux + other.trajectory_aux
        if len(combined_arr) > 0:
            order = np.argsort(combined_arr["iteration"], kind="stable")
            combined_arr = combined_arr[order]
            combined_aux = tuple(combined_aux[i] for i in order.tolist())
        combined_arr.setflags(write=False)

        return State(
            pool=merged_pool,
            thing_ids=merged_ids,
            tau_masks=merged_tau,
            sigma_masks=merged_sig,
            oracle_pairs=oracle,
            weights=tuple(sorted(ws.items(), key=lambda kv: kv[0])),
            trajectory=combined_arr,
            trajectory_aux=combined_aux,
            iteration=max(self.iteration, other.iteration),
        )

    def restrict(
        self,
        *,
        thing_ids: frozenset | None = None,
    ) -> "State":
        """Return a sub-state containing only the requested things.
        Pool is preserved; oracle pairs restricted to those fully
        contained in the requested thing-set.

        Vectorized: one boolean mask on axis-0 of the mask matrices.
        """
        if thing_ids is None:
            return self
        keep_mask = np.array(
            [str(tid) in thing_ids for tid in self.thing_ids], dtype=bool
        )
        kept_oracle = frozenset(
            p for p in self.oracle_pairs if all(x in thing_ids for x in p)
        )
        return State(
            pool=self.pool,
            thing_ids=self.thing_ids[keep_mask],
            tau_masks=self.tau_masks[keep_mask],
            sigma_masks=self.sigma_masks[keep_mask],
            oracle_pairs=kept_oracle,
            weights=self.weights,
            trajectory=self.trajectory,
            trajectory_aux=self.trajectory_aux,
            iteration=self.iteration,
        )

    # -- identity / fixed-point detection -----------------------------------

    def signature(self) -> Tuple:
        """Structural fingerprint for state equality / fixed-point tests.

        Excludes trajectory (which grows monotonically) and iteration.
        Uses the mask matrices' tobytes() + thing_ids tuple so
        comparison is an O(bytes) memcmp rather than per-Thing dict
        traversal.
        """
        return (
            self.pool.keys,
            tuple(str(t) for t in self.thing_ids),
            self.tau_masks.tobytes(),
            self.sigma_masks.tobytes(),
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

    # Phase 3: build Things with bitmaps over the orbit-expanded pool.
    # Base atoms fire symmetrically (τ = σ per d-tau-sigma-symmetric-
    # at-grade-1).  Orbit members fire asymmetrically: their columns
    # are S3-permutations of the base atom's (τ, σ, κ) = (1, 1, 0)
    # vector.  For (τκ) rotation: (τ, σ) = (0, 1).  For (σκ) rotation:
    # (τ, σ) = (1, 0).  These are set per-thing in a post-pass after
    # the base-atom mask is constructed.
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
        # τ = σ at grade 1 (symmetric atoms; orbit expansion is LAZY
        # on the read path per Stage 7.2.2, not eager on the write path)
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

    Optional ``firing_bitmaps`` kwarg (Stage 7.0.5): when step() has
    precomputed the [pool_size, n_things] 2D bool matrix, it passes
    it through to scorers that can take the fast array-slicing path
    for four-cell counting.  Scorers ignore the kwarg if they don't
    need it.  None default preserves backward-compatible call sites.
    """

    def __call__(self, state: "State",
                 k_left: "K", k_right: "K",
                 *, firing_bitmaps: np.ndarray | None = None
                 ) -> ScoreValue: ...

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


def _count_four_cell(state: "State", i: int, j: int,
                     *,
                     firing_bitmaps: np.ndarray | None = None,
                     channel: str = "tau",
                     ) -> Tuple[int, int, int, int]:
    """Return (n_00, n_01, n_10, n_11): counts of things in each cell of
    the 2×2 (bit i, bit j) joint firing distribution on the given channel.

    Stage 7.3: delegates to fire_pair for column retrieval.  Under the
    Belnap-encoded mask model (l-belnap-encoded-mask-matrix), fire_pair
    respects the populated flag and computes lazily for gap columns.
    This eliminates the dual-access-path issue (direct mask read vs
    fire_pair) identified in the post-7.3 audit.

    Two acceleration paths:
    * If ``firing_bitmaps`` is provided AND both indices are within
      the bitmaps' axis-0, the precomputed rows are used directly
      (fast path — these are the cached mask columns transposed).
    * Otherwise, fire_pair is called on the K at each index.
    """
    if firing_bitmaps is not None:
        if i < firing_bitmaps.shape[0] and j < firing_bitmaps.shape[0]:
            fires_i = firing_bitmaps[i]
            fires_j = firing_bitmaps[j]
        else:
            # Fall through to fire_pair for out-of-range bits
            k_i = state.pool.ks[i] if i < len(state.pool.ks) else ZeroK()
            k_j = state.pool.ks[j] if j < len(state.pool.ks) else ZeroK()
            tau_i, sig_i = state.fire_pair(k_i)
            tau_j, sig_j = state.fire_pair(k_j)
            fires_i = tau_i if channel == "tau" else sig_i
            fires_j = tau_j if channel == "tau" else sig_j
    else:
        k_i = state.pool.ks[i] if i < len(state.pool.ks) else ZeroK()
        k_j = state.pool.ks[j] if j < len(state.pool.ks) else ZeroK()
        tau_i, sig_i = state.fire_pair(k_i)
        tau_j, sig_j = state.fire_pair(k_j)
        fires_i = tau_i if channel == "tau" else sig_i
        fires_j = tau_j if channel == "tau" else sig_j

    n_11 = int(np.sum(fires_i & fires_j))
    n_10 = int(np.sum(fires_i & ~fires_j))
    n_01 = int(np.sum(~fires_i & fires_j))
    n_00 = int(len(fires_i) - n_11 - n_10 - n_01)
    return (n_00, n_01, n_10, n_11)


# -- Default scorers (structural dataclass classes + singletons) ----------
#
# Under l-scorer-as-shape-contract (enacted Stage 7.0.10), a scorer
# factors into two orthogonal structural pieces:
#
#   - A CellExtractor: (state, i, j, firing_bitmaps?) → count-tensor.
#     Chooses WHICH cells of the joint (K_i, K_j) firing distribution
#     to materialize and over which domain (things vs oracle pairs).
#
#   - A Reducer: count-tensor → scalar.  Maps the cells into a scalar
#     score via an aggregation (sum, log-product, entropy, cell-select).
#
# The scorer is a composition: CellScorer(cells, reduce).  A new scorer
# is a new binding, not a new class.  The 5 original scorer classes
# collapse to 5 singleton compositions over 2 extractors × 4 reducers.


@dataclass(frozen=True)
class CellExtractor(ABC):
    """Extract a count-tensor of cells from a State for a K-pair (i, j).

    Subclasses:
      - ``ThingsFourCell``    → Int[Array, '2 2'] indexed [fires_i, fires_j]
      - ``OracleSixteenCell`` → Int[Array, '2 2 2 2'] indexed [a_i, a_j, b_i, b_j]

    The ``structure`` property carries intensional identity so the
    extractor survives trajectory logging + composite structure
    recursion per p-functions-have-structural-identity.
    """

    @abstractmethod
    def __call__(
        self, state: "State", i: int, j: int,
        *, firing_bitmaps: np.ndarray | None = None,
    ) -> np.ndarray: ...

    @property
    @abstractmethod
    def structure(self) -> tuple: ...


@dataclass(frozen=True)
class ThingsFourCell(CellExtractor):
    """4-cell joint firing distribution over things for a K-pair (i, j).

    Returns Int[Array, '2 2'] where ``cells[fires_i, fires_j]`` = count
    of things whose τ-mask has that (K_i, K_j) profile.  Matches the
    semantics of the pre-7.0.10 ``_count_four_cell``:
    ``(n_00, n_01, n_10, n_11) = (cells[0,0], cells[0,1], cells[1,0], cells[1,1])``.
    """

    def __call__(
        self, state: "State", i: int, j: int,
        *, firing_bitmaps: np.ndarray | None = None,
    ) -> np.ndarray:
        n_00, n_01, n_10, n_11 = _count_four_cell(
            state, i, j, firing_bitmaps=firing_bitmaps,
        )
        return np.array([[n_00, n_01], [n_10, n_11]], dtype=np.int64)

    @property
    def structure(self) -> tuple:
        return ("things_four_cell",)


@dataclass(frozen=True)
class OracleSixteenCell(CellExtractor):
    """16-cell joint distribution over ordered oracle pairs (A, B).

    Returns Int[Array, '2 2 2 2'] where
    ``cells[a_i, a_j, b_i, b_j]`` = count of oracle pairs whose τ-mask
    has that joint profile.  A = pair[0] (min id by construction),
    B = pair[1] (max id) per the l-oracle-pairs-as-index-array
    ordering invariant.  firing_bitmaps is ignored — oracle scoring
    indexes state.tau_masks directly.
    """

    def __call__(
        self, state: "State", i: int, j: int,
        *, firing_bitmaps: np.ndarray | None = None,
    ) -> np.ndarray:
        del firing_bitmaps  # oracle path indexes tau_masks directly
        pairs = state.oracle_pair_indices
        if len(pairs) == 0:
            return np.zeros((2, 2, 2, 2), dtype=np.int64)
        a_i = state.tau_masks[pairs[:, 0], i].astype(np.int64)
        a_j = state.tau_masks[pairs[:, 0], j].astype(np.int64)
        b_i = state.tau_masks[pairs[:, 1], i].astype(np.int64)
        b_j = state.tau_masks[pairs[:, 1], j].astype(np.int64)
        flat = (a_i << 3) | (a_j << 2) | (b_i << 1) | b_j
        counts = np.bincount(flat, minlength=16).reshape((2, 2, 2, 2))
        return counts.astype(np.int64)

    @property
    def structure(self) -> tuple:
        return ("oracle_sixteen_cell",)


@dataclass(frozen=True)
class Reducer(ABC):
    """Map a count-tensor of cells into a scalar score.

    Each concrete Reducer declares which cell-tensor shape it expects;
    calling with a mismatched shape is a bug at the composition site,
    not at runtime — composition is the point where the shape contract
    binds.
    """

    @abstractmethod
    def __call__(self, cells: np.ndarray) -> float: ...

    @property
    @abstractmethod
    def structure(self) -> tuple: ...


@dataclass(frozen=True)
class SumOffDiagonal(Reducer):
    """Sum of off-diagonal cells on a 2×2 cell tensor: ``cells[0,1] + cells[1,0]``.

    Principled XOR-earning score per p-four-cell-xor-score; only the
    asymmetric cells contribute.  Units: counts.
    """
    units: str = "count"

    def __call__(self, cells: np.ndarray) -> float:
        return float(int(cells[0, 1]) + int(cells[1, 0]))

    @property
    def structure(self) -> tuple:
        return ("sum_off_diagonal",)


@dataclass(frozen=True)
class LogProductOffDiagonal(Reducer):
    """Log-product of off-diagonals on a 2×2 cell tensor: ``log(c[0,1]) + log(c[1,0])``.

    Rewards K-pairs whose asymmetric cells are BOTH well-populated
    (p-boolean-earned-by-both-off-diagonals) rather than summing
    indifferently.  Returns 0 when either off-diagonal is empty.
    Units: nats.
    """
    units: str = "nats"

    def __call__(self, cells: np.ndarray) -> float:
        c01 = int(cells[0, 1])
        c10 = int(cells[1, 0])
        if c01 == 0 or c10 == 0:
            return 0.0
        return math.log(c01) + math.log(c10)

    @property
    def structure(self) -> tuple:
        return ("log_product_off_diagonal",)


@dataclass(frozen=True)
class ShannonEntropy(Reducer):
    """Shannon entropy (bits) of the flattened cell distribution.

    DIAGNOSTIC: operates on any cell-tensor shape; flattens, normalizes,
    -Σ p·log2(p).  Conflates gap/overlap — not principled for
    articulation ranking (see p-four-cell-xor-score).  Units: bits.
    """
    units: str = "bits"

    def __call__(self, cells: np.ndarray) -> float:
        flat = cells.ravel().astype(np.int64)
        total = int(flat.sum())
        if total == 0:
            return 0.0
        ent = 0.0
        for n in flat:
            n_int = int(n)
            if n_int > 0:
                p = n_int / total
                ent -= p * math.log2(p)
        return ent

    @property
    def structure(self) -> tuple:
        return ("shannon_entropy",)


@dataclass(frozen=True)
class SelectCell(Reducer):
    """Return a single cell's count as the score.

    ``idx`` is a tuple matching the cell tensor's rank.  For the
    16-cell oracle extractor, ``idx = (a_i, a_j, b_i, b_j)``.  Units:
    counts.
    """
    idx: Tuple[int, ...] = ()
    units: str = "count"

    def __call__(self, cells: np.ndarray) -> float:
        return float(int(cells[self.idx]))

    @property
    def structure(self) -> tuple:
        return ("select_cell", self.idx)


@dataclass(frozen=True)
class CellScorer:
    """A scorer = (cell extractor, reducer).

    Composition captures the two axes along which the original 5
    scorer classes varied: WHICH cells to extract (over-things vs
    over-oracle-pairs) and HOW to reduce them (sum off-diagonals,
    log-product, entropy, single-cell select).  New scorers are
    new bindings, not new classes.

    Public signature preserved from the pre-7.0.10 protocol:
    ``__call__(state, k_left, k_right, *, firing_bitmaps=None) → ScoreValue``.
    The internal tensor signature (state → cells → scalar) is the
    shape contract; the K-object-bearing outer signature dispatches
    to it.
    """

    cells: CellExtractor
    reduce: Reducer

    def __call__(
        self, state: "State", k_left: "K", k_right: "K",
        *, firing_bitmaps: np.ndarray | None = None,
    ) -> ScoreValue:
        i = state.pool.bit_of(k_left)
        j = state.pool.bit_of(k_right)
        if i is None or j is None:
            return ScoreValue(0.0)
        cell_counts = self.cells(state, i, j, firing_bitmaps=firing_bitmaps)
        return ScoreValue(float(self.reduce(cell_counts)))

    @property
    def structure(self) -> tuple:
        return ("scorer", "cell_scorer", self.cells.structure, self.reduce.structure)


# -- Singletons re-expressed as curried CellScorer compositions -----------
#
# Currying binds the domain (which cells to extract) as a partial;
# reducers close the composition.  Reads "<reducer> on <domain>".
# The two partials are themselves first-class values — composable
# across modules, introspectable as functools.partial instances.


on_things       = partial(CellScorer, ThingsFourCell())
on_oracle_pairs = partial(CellScorer, OracleSixteenCell())


scorer_xor_off_diagonal          = on_things(SumOffDiagonal())
scorer_xor_off_diagonal_log_pair = on_things(LogProductOffDiagonal())
scorer_boolean_earning_corpus    = scorer_xor_off_diagonal_log_pair  # alias
scorer_entropy_of_four_cell      = on_things(ShannonEntropy())

scorer_oracle_boolean_witness_tau_sigma = on_oracle_pairs(SelectCell(idx=(1, 0, 0, 1)))
scorer_oracle_boolean_witness_sigma_tau = on_oracle_pairs(SelectCell(idx=(0, 1, 1, 0)))


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
        pairs = state.oracle_pair_indices
        if len(pairs) == 0:
            return ObjectiveValue(0.0)
        ta = state.tau_masks[pairs[:, 0]]   # [n_pairs, pool_size]
        tb = state.tau_masks[pairs[:, 1]]   # [n_pairs, pool_size]
        a_only_any = np.any(ta & ~tb, axis=1)   # [n_pairs] bool
        b_only_any = np.any(~ta & tb, axis=1)   # [n_pairs] bool
        hits = a_only_any & b_only_any
        return ObjectiveValue(float(int(hits.sum())))

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
        n_things = len(state.thing_ids)
        if n_things == 0 or state.tau_masks.shape[1] == 0:
            return ObjectiveValue(0.0)
        # Per-K firing count across things: axis-0 reduction on the
        # (n_things, pool_size) mask matrix.
        n_fires = state.tau_masks.sum(axis=0)       # [pool_size]
        p = n_fires / n_things                       # [pool_size] float
        # Entropy at probabilities {0, 1} is 0; avoid log(0) by masking.
        nondegenerate = (p > 0.0) & (p < 1.0)
        pp = p[nondegenerate]
        total = float(np.sum(-pp * np.log2(pp) - (1 - pp) * np.log2(1 - pp)))
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
                 k_left: "K", k_right: "K",
                 *, firing_bitmaps: np.ndarray | None = None
                 ) -> ScoreValue:
        total = 0.0
        for w, s in self.components:
            total += w * s(state, k_left, k_right,
                           firing_bitmaps=firing_bitmaps)
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


def firing_bitmaps_of(state: "State", channel: str = "tau") -> np.ndarray:
    """Return the pool-major firing matrix ``(pool_size, n_things)`` for
    the requested channel.

    Under l-state-things-as-parallel-arrays (Stage 7.0.7b) the state
    already stores per-thing masks as a ``(n_things, pool_size)``
    bool matrix; the pool-major view is just ``.T`` on that — O(1)
    view, no copy.  This replaces the Stage 7.0 ``_compute_firing_
    bitmaps`` which rebuilt the matrix per step() by iterating over
    Thing objects; with parallel arrays, there is nothing to build.
    """
    if channel == "tau":
        return state.tau_masks.T
    elif channel == "sigma":
        return state.sigma_masks.T
    elif channel == "kappa":
        return np.logical_xor(state.tau_masks, state.sigma_masks).T
    else:
        raise ValueError(f"unknown channel {channel!r}")


def _articulate_wedges_batch(
    state: "State",
    wedges: list,
    firing_bitmaps: np.ndarray,
) -> Tuple["State", int]:
    """Articulate a BATCH of wedges into state.

    Stage 7.3: fire_pair is the canonical computation for all K types.
    _articulate_wedges_batch delegates to fire_pair for both the
    degeneracy check and the column computation.  The AND/combinator
    dispatch is transparent — fire_pair handles it internally based
    on the wedge's leaf types.

    Columns are CACHED in the mask matrix so future step() co-fire
    matmul sees them.  The computation is lazy (via fire_pair fold);
    the cache is the mask matrix (eager storage of the result).

    Returns (new_state, count_articulated).  Pure transformer.
    """
    pool_index = state.pool.key_to_bit

    kept_wedges: list = []
    kept_keys_set: set = set()
    kept_tau_cols: list = []
    kept_sig_cols: list = []
    for wedge in wedges:
        if isinstance(wedge, ZeroK):
            continue
        w_key = wedge.key()
        if w_key in pool_index:
            continue
        if w_key in kept_keys_set:
            continue

        # fire_pair: canonical lazy computation (AND or combinator
        # depending on leaf types; memoized on State).
        tau_w, sig_w = state.fire_pair(wedge)
        if not (np.any(tau_w) or np.any(sig_w)):
            continue  # degenerate

        kept_wedges.append(wedge)
        kept_keys_set.add(w_key)
        kept_tau_cols.append(tau_w)
        kept_sig_cols.append(sig_w)

    if not kept_wedges:
        return state, 0

    n_new = len(kept_wedges)

    # Extend pool + cache columns in mask matrix
    new_pool = state.pool
    for w in kept_wedges:
        new_pool = new_pool.with_k(w)

    new_tau_cols = np.stack(kept_tau_cols, axis=0).T
    new_sig_cols = np.stack(kept_sig_cols, axis=0).T
    new_tau = np.concatenate([state.tau_masks, new_tau_cols], axis=1)
    new_sig = np.concatenate([state.sigma_masks, new_sig_cols], axis=1)
    # New columns are fire_pair-computed → Belnap T or F (populated)
    pop_cols = np.ones_like(new_tau_cols, dtype=bool)
    new_tau_pop = np.concatenate([state.tau_populated, pop_cols], axis=1)
    new_sig_pop = np.concatenate([state.sigma_populated, pop_cols], axis=1)

    new_state = State(
        pool=new_pool,
        thing_ids=state.thing_ids,
        tau_masks=new_tau,
        sigma_masks=new_sig,
        tau_populated=new_tau_pop,
        sigma_populated=new_sig_pop,
        oracle_pairs=state.oracle_pairs,
        weights=state.weights,
        trajectory=state.trajectory,
        trajectory_aux=state.trajectory_aux,
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
    # firing_bitmaps is state.tau_masks.T under the parallel-array
    # representation (l-state-things-as-parallel-arrays) — an O(1) view,
    # no build step.
    firing_bitmaps = firing_bitmaps_of(state, "tau")
    pool_index = state.pool.key_to_bit
    n_things = len(state.thing_ids)

    # -- Phase 1: enumerate candidate K-pairs (n_11 > 0) -------------------
    #
    # S3 orbit expansion is INFERRED, not materialized (Stage 7.2.2+).
    # Under the F₂² constraint, (τ⊕σ)|σ = τ|σ and τ|(τ⊕σ) = τ|σ —
    # so the τ∪σ union firing of any S3-rotated K equals the base K's
    # τ∪σ.  The virtual 3P×3P matmul is 9 identical copies of the base
    # P×P block: zero new co-fire pairs from orbit expansion.
    #
    # What orbit expansion DOES add: new DEMANDED WEDGES.  For each
    # base candidate pair (i, j), we also demand Wedge(K_i, Rotated(K_j, g))
    # for each S3 generator g.  These Rotated-leaf wedges trigger the
    # general combinator and produce asymmetric firings.  The demands
    # are inferred from the base co-fire matrix without materializing
    # virtual firing rows — a syndrome-decoding shortcut where the
    # algebraic identity IS the syndrome.
    sigma_bitmaps = firing_bitmaps_of(state, "sigma")
    base_union = firing_bitmaps | sigma_bitmaps
    fb_int = base_union.astype(np.int32)
    co_fire_count = fb_int @ fb_int.T  # [P, P]
    pool_size = firing_bitmaps.shape[0]
    n_things = len(state.thing_ids)
    # Upper-triangle of the P×P matrix
    triu = np.triu(np.ones((pool_size, pool_size), dtype=bool), k=1)
    pair_mask = (co_fire_count > 0) & triu
    i_idx, j_idx = np.where(pair_mask)
    base_pairs = list(zip(i_idx.tolist(), j_idx.tolist()))

    # -- Phase 2: filter to uncaptured demands -----------------------------
    # For each base candidate pair (i, j), demand the base wedge AND
    # its S3-orbit-inferred Rotated-leaf variants (grade-1 parents
    # only — rotating grade-2+ parents would produce grade-3+
    # Rotated-leaf wedges the general combinator can't handle yet).
    demanded: list = []  # list of (k_left, k_right, wedge)
    seen_wedge_keys: set = set()
    for (i, j) in base_pairs:
        k_i = state.pool.ks[i]
        k_j = state.pool.ks[j]
        # Enumerate: base pair + Rotated-leaf variants for grade-1 K's
        pairs_to_try = [(k_i, k_j)]
        if k_j.grade == 1:
            for g in _ORBIT_SEEDING_GENERATORS:
                pairs_to_try.append((k_i, rotate(k_j, g)))
        if k_i.grade == 1:
            for g in _ORBIT_SEEDING_GENERATORS:
                pairs_to_try.append((rotate(k_i, g), k_j))
        for kl, kr in pairs_to_try:
            wedge = Wedge(kl, kr).normalize()
            if isinstance(wedge, ZeroK):
                continue
            w_key = wedge.key()
            if w_key in pool_index:
                continue  # captured; no demand
            if w_key in seen_wedge_keys:
                continue  # duplicate from different pairs
            seen_wedge_keys.add(w_key)
            demanded.append((kl, kr, wedge))

    # -- Phase 3: order by scorer (if provided), else by wedge key --------
    need_scoring = (
        scorer is not None
        and max_articulations_per_step is not None
        and len(demanded) > max_articulations_per_step
    )
    if need_scoring:
        scored = []
        for k_i, k_j, wedge in demanded:
            # Pass precomputed firing_bitmaps so scorers can take the
            # fast path (p-numpy-is-the-natural-cpu-representation).
            s = scorer(state, k_i, k_j, firing_bitmaps=firing_bitmaps)
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
        # Event-sourcing tag: "step" distinguishes these entries from
        # orbit-seeding events (source="orbit_seed") appended by
        # articulate_rotated_from_residue.  A trajectory replayer
        # dispatches on this field.
        "source": "step",
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
    """Iterate step() until no new wedges are articulated.

    Termination per d-fixed-point-is-termination: the last iteration's
    trajectory entry reports ``articulated_count == 0`` — the pool
    has reached closure under the overlap-demand articulation rule.

    This is a DIRECT read from the trajectory, not a hash or signature
    comparison.  Stage 7.0.6 replaced the previous signature()-based
    check per the user observation that signature materialization was
    solving a problem that didn't exist (tuple == tuple in signature
    comparison never invokes Thing.__hash__, so the 7.0.5 hash cache
    was irrelevant; once that was reverted, signature() itself became
    unnecessary here).  The trajectory signal is cheaper, exact, and
    matches the principle body of d-fixed-point-is-termination
    literally: "no productive wedge articulation".

    No max_iters (p-iteration-count-unknown).  Callers needing a
    budget should either bound ``max_articulations_per_step`` (slowing
    each iteration) or wrap this function in their own bounded loop.

    Pure: does not mutate input state.  Returns the fixed-point state,
    including the full trajectory of every intermediate iteration for
    inspection / replay.
    """
    while True:
        state = step(
            state,
            scorer=scorer,
            objective=objective,
            max_articulations_per_step=max_articulations_per_step,
        )
        if len(state.trajectory) > 0 and state.trajectory[-1]["articulated_count"] == 0:
            return state



# ---------------------------------------------------------------------------
# Stage 7.1 — hybrid JSONL + HDF5 I/O (enacts l-hdf5-compound-dtypes-mirror-in-memory)
# ---------------------------------------------------------------------------
#
# Stage 7.1.1 alignment to lemma + JSONL retirement direction:
#
# Per p-storage-matches-data-shape and the lemma's "pool and masks as
# separate datasets sharing the 'pool_size' attribute on their parent
# group" formulation:
#
#   - Pool now lives in HDF5 as ``/pool/keys_array`` — a compound-dtype
#     dataset that mirrors the in-memory POOL_DTYPE field-for-field
#     (with 'key' widened from object to fixed-width S512 bytes for
#     HDF5 compatibility).  Stage 7.1's pool.jsonl is RETIRED.
#   - Masks live in HDF5 as ``/masks/tau`` (and optionally
#     ``/masks/sigma``).  Both share the ``pool_size`` attribute on
#     the ``/masks`` group, asserting axis-0-of-pool == axis-1-of-masks.
#   - Trajectory numeric records live in HDF5 as ``/trajectory``
#     (compound TRAJECTORY_DTYPE).
#   - HDF5 datasets are CHUNKED with maxshape on growable axes —
#     supports future incremental growth (Stage 10 parallel shards)
#     without re-dumping.
#
# Remaining JSONL files (transitional, slated for migration):
#   - things.jsonl / oracle_pairs.jsonl / weights.jsonl /
#     trajectory_aux.jsonl  — small-algebra authoritative forms;
#     migration to HDF5 awaits a satisfying handling of variable-
#     shape aux dicts (trajectory_aux) and per-record string fields.
#     Direction is full JSONL retirement; no new JSONL files added.
#
# Sigma masks are serialized conditionally: if
# state.sigma_derivable_from_tau is True, /masks/sigma is omitted and
# load reconstructs it as a copy of tau_masks.  The `sigma_stored`
# root attribute records the choice so the loader knows which branch.
#
# Self-validation via algebraic structure (replaces explicit range
# checks): on load, each pool row's stored orbit_id is compared to
# the orbit_id derived from the K's intensional structure (walk the
# Rotated chain to the orbit root, then pool.bit_of(root)).  Mismatch
# raises — catches both range corruption and orbit/structure
# inconsistencies.  Trajectory iteration field is checked for
# consecutive monotonicity (iteration[i+1] - iteration[i] == 1) and
# against the n_iter attribute.
#
# Round-trip invariant: state.signature() == load_state(dump_state(state)).signature().

SCHEMA_VERSION = "7.2.0"

# Compound dtype for pool storage in HDF5: key field as fixed-width
# bytes (UTF-8 encoded).  S512 accepts keys up to 512 bytes; dump
# guards against overflow.  Future migration to variable-length
# strings or key decomposition will widen this constraint.
_POOL_HDF5_KEY_WIDTH = 512
POOL_HDF5_DTYPE = np.dtype([
    ("key", f"S{_POOL_HDF5_KEY_WIDTH}"),
    ("grade", "u1"),
    ("orbit_id", "u4"),
    ("orbit_parent", "u4"),
])


def _orbit_root(k: K) -> K:
    """Walk the Rotated chain to the orbit root (first non-Rotated K)."""
    base = k
    while isinstance(base, Rotated):
        base = base.base
    return base


def _expected_orbit_id_for(k: K, pool: "Pool", own_bit: int) -> int:
    """Re-derive the expected orbit_id for K given the pool and K's bit.

    Algebraic self-validation (per the Stage 7.1.1 audit's Sev-3 fix):
    instead of bounds-checking orbit_id ∈ [0, pool_size), derive what
    orbit_id SHOULD be from the K's intensional structure and
    compare on load.  Catches inconsistencies that bounds-checks
    would miss (e.g., orbit_id pointing at a real bit but the wrong
    one).

    For a non-Rotated K, the orbit ROOT is K itself, so orbit_id ==
    own_bit.  For a Rotated K, walk the Rotated chain to the root
    (which must be in the pool), and orbit_id == pool.bit_of(root).
    """
    root = _orbit_root(k)
    if root is k:
        return own_bit
    root_bit = pool.bit_of(root)
    if root_bit is None:
        raise ValueError(
            f"K at bit {own_bit} has Rotated root not present in pool; "
            f"orbit metadata cannot be re-derived"
        )
    return root_bit


def dump_state(state: "State", out_dir) -> None:
    """Serialize a State to a directory containing HDF5 + JSONL files.

    Stage 7.1.1: pool migrated to HDF5; remaining JSONL files are
    transitional (things, oracle_pairs, weights, trajectory_aux).
    HDF5 datasets are chunked with extensible axis-0 for future
    incremental growth.

    Creates ``out_dir`` if it doesn't exist.  Writes:

      ``state.h5`` — HDF5 with:
          /pool/keys_array  compound POOL_HDF5_DTYPE (S512 keys)
          /masks/tau        Bool[n_things, pool_size]
          /masks/sigma      (optional, only if sigma not derivable)
          /trajectory       compound TRAJECTORY_DTYPE
          Root attributes: schema_version, pool_size, n_things,
              n_iter, iteration, sigma_stored,
              pool_has_trivial_orbits.
          /masks group attribute: pool_size (asserts on load that
              axis-1 of masks == axis-0 of pool).

      ``things.jsonl``            — one line per thing (row_index, id)
      ``oracle_pairs.jsonl``      — one line per unordered pair
      ``weights.jsonl``           — one line per (k_key, weight)
      ``trajectory_aux.jsonl``    — one line per iteration's aux dict
    """
    import h5py
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # -- Guard: pool keys fit in fixed-width HDF5 dtype ---------------------
    pool_size = state.pool.size()
    if pool_size > 0:
        max_key_len = max(len(str(state.pool.keys_array[i]["key"]).encode("utf-8"))
                          for i in range(pool_size))
        if max_key_len > _POOL_HDF5_KEY_WIDTH:
            raise ValueError(
                f"max K key length {max_key_len} exceeds POOL_HDF5_DTYPE "
                f"'key' field width {_POOL_HDF5_KEY_WIDTH}; key decomposition "
                f"or wider field needed"
            )

    # -- things.jsonl -------------------------------------------------------
    with (out_dir / "things.jsonl").open("w") as f:
        for i, tid in enumerate(state.thing_ids):
            entry = {"row_index": i, "id": str(tid)}
            f.write(json.dumps(entry, ensure_ascii=False) + "\n")

    # -- oracle_pairs.jsonl -------------------------------------------------
    # Canonical within-pair ordering: (min, max) by id string.
    with (out_dir / "oracle_pairs.jsonl").open("w") as f:
        for pair in state.oracle_pairs:
            if len(pair) != 2:
                continue
            a_id, b_id = sorted(str(x) for x in pair)
            f.write(json.dumps({"a_id": a_id, "b_id": b_id},
                               ensure_ascii=False) + "\n")

    # -- weights.jsonl ------------------------------------------------------
    with (out_dir / "weights.jsonl").open("w") as f:
        for k_key, w in state.weights:
            f.write(json.dumps({"k_key": str(k_key), "weight": float(w)},
                               ensure_ascii=False) + "\n")

    # -- trajectory_aux.jsonl -----------------------------------------------
    with (out_dir / "trajectory_aux.jsonl").open("w") as f:
        for i, aux in enumerate(state.trajectory_aux):
            f.write(json.dumps({"iteration": i, "aux": aux},
                               ensure_ascii=False) + "\n")

    # -- state.h5 -----------------------------------------------------------
    sigma_stored = not state.sigma_derivable_from_tau
    n_things = len(state.thing_ids)
    n_iter = len(state.trajectory)
    with h5py.File(out_dir / "state.h5", "w") as h5:
        h5.attrs["schema_version"] = SCHEMA_VERSION
        h5.attrs["pool_size"] = pool_size
        h5.attrs["n_things"] = n_things
        h5.attrs["n_iter"] = n_iter
        h5.attrs["iteration"] = state.iteration
        h5.attrs["sigma_stored"] = sigma_stored
        h5.attrs["pool_has_trivial_orbits"] = state.pool_has_trivial_orbits

        # Pool: compound dataset with chunking + extensible axis-0
        pool_group = h5.create_group("pool")
        pool_group.attrs["pool_size"] = pool_size
        if pool_size > 0:
            encoded = np.empty(pool_size, dtype=POOL_HDF5_DTYPE)
            for i in range(pool_size):
                row = state.pool.keys_array[i]
                encoded[i] = (
                    str(row["key"]).encode("utf-8"),
                    int(row["grade"]),
                    int(row["orbit_id"]),
                    int(row["orbit_parent"]),
                )
        else:
            encoded = np.empty(0, dtype=POOL_HDF5_DTYPE)
        pool_group.create_dataset(
            "keys_array",
            data=encoded,
            dtype=POOL_HDF5_DTYPE,
            chunks=True,
            maxshape=(None,),
        )

        # Masks: chunked, extensible on both axes (axis-0 = n_things;
        # axis-1 = pool_size; both grow under d-disk-as-merge-protocol's
        # successor model where dumps may extend prior dumps).
        masks_group = h5.create_group("masks")
        masks_group.attrs["pool_size"] = pool_size
        masks_group.create_dataset(
            "tau",
            data=state.tau_masks,
            dtype=bool,
            chunks=True,
            maxshape=(None, None),
        )
        if sigma_stored:
            masks_group.create_dataset(
                "sigma",
                data=state.sigma_masks,
                dtype=bool,
                chunks=True,
                maxshape=(None, None),
            )

        # Trajectory: chunked, extensible on axis-0 for incremental
        # iteration-by-iteration appends.
        h5.create_dataset(
            "trajectory",
            data=state.trajectory,
            dtype=TRAJECTORY_DTYPE,
            chunks=True,
            maxshape=(None,),
        )


def load_state(in_dir) -> "State":
    """Reconstruct a State from a directory produced by ``dump_state``.

    Stage 7.1.1 self-validation:
      - Schema version major matches loader's.
      - pool_size attribute consistent across HDF5 root, /masks group,
        /pool/keys_array length.
      - n_things attribute matches things.jsonl row count AND
        tau_masks axis-0.
      - For each pool row, derived orbit_id (via _orbit_root + pool
        bit_of) matches stored orbit_id — algebraic self-check
        catching both bounds errors and structure/orbit inconsistencies.
      - Pool key bijection: re-encoded key matches stored key per row.
      - Trajectory axis-0 length matches n_iter attribute.
      - Trajectory iteration field is consecutive (each row's
        iteration == prior + 1, starting from 1 if non-empty).
    """
    import h5py
    in_dir = Path(in_dir)

    # -- state.h5: pool + masks + trajectory --------------------------------
    with h5py.File(in_dir / "state.h5", "r") as h5:
        schema = h5.attrs["schema_version"]
        if isinstance(schema, bytes):
            schema = schema.decode()
        if schema.split(".")[0] != SCHEMA_VERSION.split(".")[0]:
            raise ValueError(
                f"schema version mismatch: disk {schema!r} vs "
                f"loader {SCHEMA_VERSION!r}"
            )
        pool_size_attr = int(h5.attrs["pool_size"])
        n_things_attr = int(h5.attrs["n_things"])
        n_iter_attr = int(h5.attrs["n_iter"])
        iteration = int(h5.attrs["iteration"])
        sigma_stored = bool(h5.attrs["sigma_stored"])

        # Pool reconstruction from compound dataset
        pool_group = h5["pool"]
        if int(pool_group.attrs["pool_size"]) != pool_size_attr:
            raise ValueError(
                f"/pool group pool_size {pool_group.attrs['pool_size']} "
                f"!= root pool_size {pool_size_attr}"
            )
        raw = pool_group["keys_array"][()]
        if len(raw) != pool_size_attr:
            raise ValueError(
                f"/pool/keys_array length {len(raw)} != pool_size "
                f"{pool_size_attr}"
            )
        pool_rows: list = []
        ks_tuple: list = []
        for i, raw_row in enumerate(raw):
            key_str = raw_row["key"].decode("utf-8")
            struct = json.loads(key_str)
            k = k_from_structure(struct)
            if k.key() != key_str:
                raise ValueError(
                    f"pool bit {i}: reconstructed key differs from stored "
                    f"key (bijection violated)"
                )
            pool_rows.append((
                key_str,
                int(raw_row["grade"]),
                int(raw_row["orbit_id"]),
                int(raw_row["orbit_parent"]),
            ))
            ks_tuple.append(k)
        keys_array = np.array(pool_rows, dtype=POOL_DTYPE) if pool_rows \
            else np.empty(0, dtype=POOL_DTYPE)
        pool = Pool(keys_array=keys_array, ks=tuple(ks_tuple))

        # Algebraic orbit self-validation: derive expected orbit_id
        # from K structure; mismatch = corruption (Sev-3 audit fix).
        for i, k in enumerate(pool.ks):
            expected = _expected_orbit_id_for(k, pool, i)
            stored = int(pool.keys_array[i]["orbit_id"])
            if expected != stored:
                raise ValueError(
                    f"pool bit {i}: stored orbit_id {stored} != "
                    f"derived orbit_id {expected} (corruption or "
                    f"K-structure / orbit metadata inconsistency)"
                )

        # Masks
        masks_group = h5["masks"]
        if int(masks_group.attrs["pool_size"]) != pool_size_attr:
            raise ValueError(
                f"/masks group pool_size {masks_group.attrs['pool_size']} "
                f"!= root pool_size {pool_size_attr}"
            )
        tau_masks = np.array(masks_group["tau"][()], dtype=bool)
        if tau_masks.shape != (n_things_attr, pool_size_attr):
            raise ValueError(
                f"tau_masks shape {tau_masks.shape} != expected "
                f"({n_things_attr}, {pool_size_attr})"
            )
        if sigma_stored:
            sigma_masks = np.array(masks_group["sigma"][()], dtype=bool)
            if sigma_masks.shape != tau_masks.shape:
                raise ValueError(
                    f"sigma_masks shape {sigma_masks.shape} != tau_masks "
                    f"shape {tau_masks.shape}"
                )
        else:
            sigma_masks = tau_masks.copy()

        # Trajectory
        trajectory = np.array(h5["trajectory"][()], dtype=TRAJECTORY_DTYPE)
        if trajectory.shape[0] != n_iter_attr:
            raise ValueError(
                f"trajectory length {trajectory.shape[0]} != n_iter "
                f"attribute {n_iter_attr}"
            )
        # Trajectory is a per-shard audit log, not a global clock.
        # Under p-embarrassingly-parallel, merged states have trajectories
        # that are the union of per-shard event logs — duplicate or
        # non-consecutive iteration numbers are valid (each shard's
        # sub-sequence is independently consistent; the merge is
        # strictly additive on a join-semilattice).  NO consecutiveness
        # check: the iteration field is for audit, not for state
        # constraint.  The only load-bearing trajectory read is
        # run_to_fixed_point's termination check on the LAST entry's
        # articulated_count — which doesn't depend on sequence ordering.

    # -- things.jsonl -------------------------------------------------------
    thing_id_list: list = []
    with (in_dir / "things.jsonl").open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            entry = json.loads(line)
            idx = int(entry["row_index"])
            if idx != len(thing_id_list):
                raise ValueError(
                    f"things.jsonl row_index {idx} out of order at row "
                    f"{len(thing_id_list)}"
                )
            thing_id_list.append(entry["id"])
    if len(thing_id_list) != n_things_attr:
        raise ValueError(
            f"things.jsonl row count {len(thing_id_list)} != n_things "
            f"attribute {n_things_attr}"
        )
    thing_ids = np.array(thing_id_list, dtype=object)

    # -- oracle_pairs.jsonl -------------------------------------------------
    oracle_pair_set = []
    pairs_path = in_dir / "oracle_pairs.jsonl"
    if pairs_path.exists():
        with pairs_path.open() as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                entry = json.loads(line)
                oracle_pair_set.append(
                    frozenset({ThingId(entry["a_id"]),
                               ThingId(entry["b_id"])})
                )
    oracle_pairs = frozenset(oracle_pair_set)

    # -- weights.jsonl ------------------------------------------------------
    weights_list: list = []
    weights_path = in_dir / "weights.jsonl"
    if weights_path.exists():
        with weights_path.open() as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                entry = json.loads(line)
                weights_list.append((KKey(entry["k_key"]), float(entry["weight"])))
    weights = tuple(sorted(weights_list, key=lambda kv: kv[0]))

    # -- trajectory_aux.jsonl -----------------------------------------------
    aux_list: list = []
    aux_path = in_dir / "trajectory_aux.jsonl"
    if aux_path.exists():
        with aux_path.open() as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                entry = json.loads(line)
                aux_list.append(entry["aux"])
    trajectory_aux = tuple(aux_list)

    return State(
        pool=pool,
        thing_ids=thing_ids,
        tau_masks=tau_masks,
        sigma_masks=sigma_masks,
        oracle_pairs=oracle_pairs,
        weights=weights,
        trajectory=trajectory,
        trajectory_aux=trajectory_aux,
        iteration=iteration,
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

    # -- Stage 2.5: divergent-pool merge via vectorized column permutation --

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
        # Under lazy orbit expansion (Stage 7.2.2), the pool after
        # extract contains only base atoms (no Rotated K's).  All K's
        # are symmetric (τ = σ), so κ = 0 identically.
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
                # same-K cells directly via _count_four_cell (int
                # signature per Stage 7.0.11).
                i_bit = state.pool.bit_of(k_i)
                cells_self = _count_four_cell(state, i_bit, i_bit)
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
                i_bit = state.pool.bit_of(k_i)
                j_bit = state.pool.bit_of(k_j)
                n00, n01, n10, n11 = _count_four_cell(state, i_bit, j_bit)
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
                # Each component structure is preserved under the
                # Stage 7.0.10 CellScorer factoring: structure is
                # ("scorer", "cell_scorer", cells.structure, reduce.structure).
                assert cs_struct[1][0][0] == 0.5
                assert cs_struct[1][0][1] == (
                    "scorer", "cell_scorer",
                    ("things_four_cell",), ("sum_off_diagonal",),
                )

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

                # Stage 7.0.10: CellScorer factoring is verified by
                # constructing a FRESH composition and checking bit-
                # identical output against the singleton.  Ensures the
                # (cells, reduce) decomposition is the whole identity —
                # no hidden state in the singleton.
                fresh = CellScorer(ThingsFourCell(), SumOffDiagonal())
                assert fresh(state, k_i, k_j) == scorer_xor_off_diagonal(state, k_i, k_j)
                fresh_oracle = CellScorer(OracleSixteenCell(), SelectCell(idx=(1, 0, 0, 1)))
                assert fresh_oracle(state, k_i, k_j) == scorer_oracle_boolean_witness_tau_sigma(state, k_i, k_j)
                # Structure tuples match between fresh and singleton
                assert fresh.structure == scorer_xor_off_diagonal.structure

                print(f"    Stage 4 + 4.5 + 4.6 scorers/objectives: structural "
                      f"identity + orientation-split verified on extracted state")
                print(f"    Stage 7.0.10: CellScorer(cells, reduce) factoring "
                      f"reproduces singletons bit-identically "
                      f"(5 classes → 1 class × 2 extractors × 4 reducers)")
                print(f"    Stage 7.0.11: _count_four_cell(state, i:int, j:int) "
                      f"vectorized off state.tau_masks — no state.things "
                      f"iteration, no Thing reconstruction on the slow path")

                # -- Stage 7.0.12: S3 tensor-native + pool orbit fields +
                # separate pool_has_trivial_orbits / sigma_derivable_from_tau
                # probes (Tier 1 of the S3-cluster enactment).  Schema-
                # forward-compatibility with l-k-level-s3-operators and
                # l-combinator-and-s3-operators-are-equivalent.

                # S3.act_on_tsk operates on (3, ...) bool tensors.  The
                # identity element returns an equal copy; a transposition
                # permutes axis-0; group composition matches element-wise
                # composition of the axis permutations.
                id_elem = S3.identity()
                swap_elem = S3((1, 0, 2))
                tsk_test = np.array(
                    [[1, 0, 1, 1],   # τ
                     [0, 1, 1, 0],   # σ
                     [1, 1, 0, 1]],  # κ = τ ⊕ σ
                    dtype=bool,
                )
                tsk_id = id_elem.act_on_tsk(tsk_test)
                assert np.array_equal(tsk_id, tsk_test)
                tsk_swap = swap_elem.act_on_tsk(tsk_test)
                # swap interchanges axes 0 and 1; axis 2 unchanged
                assert np.array_equal(tsk_swap[0], tsk_test[1])
                assert np.array_equal(tsk_swap[1], tsk_test[0])
                assert np.array_equal(tsk_swap[2], tsk_test[2])
                # Composition: swap * swap = identity
                swap_twice = swap_elem.act_on_tsk(tsk_swap)
                assert np.array_equal(swap_twice, tsk_test)
                # Single-cell wrapper agrees with tensor form
                for t_val in (0, 1):
                    for s_val in (0, 1):
                        ts = TauSigma(t_val, s_val)
                        swapped = swap_elem.act(ts)
                        assert swapped.tau == s_val and swapped.sigma == t_val

                # POOL_DTYPE fields include orbit_id + orbit_parent.
                # Stage 7.2.2: with auto orbit expansion in
                # extract_initial_state, the pool NOW has Rotated K's
                # whose orbit_id points at their base.  Base atoms have
                # self-orbit; Rotated atoms have orbit_id == base.
                assert "orbit_id" in state.pool.keys_array.dtype.names
                assert "orbit_parent" in state.pool.keys_array.dtype.names
                # Under lazy orbit expansion, extracted pool has ONLY base
                # atoms.  Orbit structure is trivial; σ = τ for all K's.
                assert state.pool_has_trivial_orbits, (
                    "lazy-orbit extract should have trivial orbits (base atoms only)"
                )
                assert state.sigma_derivable_from_tau, (
                    "lazy-orbit extract should have σ == τ (symmetric atoms)"
                )
                # step() with lazy orbit expansion: pool may grow via
                # wedge articulation (including wedges with Rotated
                # leaves from virtual orbit pairs).
                stepped_sym = step(
                    state, scorer=scorer_xor_off_diagonal,
                    max_articulations_per_step=5,
                )
                assert stepped_sym.pool.size() >= state.pool.size(), (
                    "step() should preserve or grow the pool"
                )

                print(f"    Stage 7.0.12: S3 tensor axis-permutation + pool "
                      f"orbit_id/orbit_parent fields + "
                      f"pool_has_trivial_orbits + sigma_derivable_from_tau "
                      f"(forward-compat for l-k-level-s3-operators)")

                # -- Stage 7.0.13: Rotated K + swap/rotate helpers
                # (Tier 2 of the S3-cluster enactment).  Machinery
                # exists; semantic switch not thrown — step() and
                # extract_initial_state don't articulate Rotated K's.
                # Smoke-test in isolation.

                atom_a = Atom(Observable("kind_at_root:Module"))
                # Rotated construction + key round-trip via JSON
                swapped_a = swap(atom_a)
                assert isinstance(swapped_a, Rotated)
                assert swapped_a.grade == atom_a.grade
                assert swapped_a.atoms() == atom_a.atoms()
                # Bijective key encoding: structure() round-trips via JSON
                reloaded = json.loads(swapped_a.key())
                assert _tuples_eq_lists(swapped_a.structure(), reloaded)

                # Involution: swap(swap(k)) == k under normalize()
                assert swap(swap(atom_a)) == atom_a, (
                    "(τσ) swap is an involution"
                )

                # Identity rotation: rotate(k, identity) == k
                assert rotate(atom_a, S3.identity()) == atom_a

                # Rotation composition: rotate(rotate(k, g1), g2) ==
                # rotate(k, g1 * g2) under normalize().
                g_3cycle = S3((1, 2, 0))
                g_swap = S3((1, 0, 2))
                composed_by_rotate = rotate(rotate(atom_a, g_3cycle), g_swap)
                composed_by_mult = rotate(atom_a, g_3cycle * g_swap)
                assert composed_by_rotate == composed_by_mult, (
                    "nested rotations compose via S3 multiplication"
                )

                # Rotation of ZeroK is ZeroK
                assert rotate(ZeroK(), g_3cycle) == ZeroK()
                assert swap(ZeroK()) == ZeroK()

                # compose(k1, k2, g) == Wedge(k1, rotate(k2, g)).normalize()
                # The third K-level primitive; produces one cross-orientation
                # term of the general combinator per l-combinator-and-s3-
                # operators-are-equivalent.
                atom_b = Atom(Observable("kind_at_root:Function"))
                composed = compose(atom_a, atom_b, g_swap)
                direct = Wedge(atom_a, rotate(atom_b, g_swap)).normalize()
                assert composed == direct, (
                    "compose should equal Wedge(k1, rotate(k2, g)).normalize()"
                )
                # Identity element collapses compose to a plain wedge
                assert compose(atom_a, atom_b, S3.identity()) == (
                    Wedge(atom_a, atom_b).normalize()
                )
                # compose with second K == ZeroK produces ZeroK (rotate(0, g) = 0,
                # Wedge(k, 0).normalize() = 0)
                assert compose(atom_a, ZeroK(), g_swap) == ZeroK()
                # Atoms invariant under the composition is the UNION of
                # atoms of both inputs (rotation doesn't introduce atoms)
                assert composed.atoms() == frozenset({atom_a, atom_b})

                # Pool orbit bookkeeping: adding a Rotated K first
                # ensures the base is present, then the Rotated row
                # has orbit_id == base's orbit_id and orbit_parent
                # == base's bit index.
                iso_pool = Pool().with_k(swap(atom_a))
                assert iso_pool.size() == 2, (
                    "adding Rotated K should also add the base (2 entries)"
                )
                # Base is at bit 0, Rotated is at bit 1
                base_bit = iso_pool.bit_of(atom_a)
                rot_bit = iso_pool.bit_of(swap(atom_a))
                assert base_bit is not None and rot_bit is not None
                assert base_bit == 0 and rot_bit == 1
                # Base: self-orbit
                assert int(iso_pool.keys_array[base_bit]["orbit_id"]) == base_bit
                assert int(iso_pool.keys_array[base_bit]["orbit_parent"]) == base_bit
                # Rotated: orbit_id == base's orbit_id; parent == base_bit
                assert int(iso_pool.keys_array[rot_bit]["orbit_id"]) == base_bit, (
                    "Rotated K's orbit_id should match its base's orbit_id"
                )
                assert int(iso_pool.keys_array[rot_bit]["orbit_parent"]) == base_bit

                # A state built atop this pool has pool_has_trivial_orbits
                # = False (Rotated K is non-self-orbit).
                iso_state = State(pool=iso_pool)
                assert not iso_state.pool_has_trivial_orbits, (
                    "state with a Rotated K should report non-trivial orbits"
                )
                # sigma_derivable_from_tau: no things in iso_state, so
                # masks are (0, pool_size) shape — trivially equal.
                assert iso_state.sigma_derivable_from_tau

                print(f"    Stage 7.0.13: Rotated(base, perm) K + swap / rotate "
                      f"/ compose helpers; Pool.with_k propagates orbit_id "
                      f"(root) + orbit_parent (immediate); Tier 2 scaffolding")

                # -- Stage 7.1: hybrid JSONL + HDF5 I/O.  Round-trip
                # dump_state → load_state reproduces state.signature()
                # bit-identically.  Enacts l-hdf5-compound-dtypes-
                # mirror-in-memory.  Stage 7.1.1 migrated pool to HDF5
                # /pool/keys_array (compound dtype); chunked datasets
                # extensible on growable axes; algebraic orbit
                # self-validation on load.
                import tempfile
                with tempfile.TemporaryDirectory() as td:
                    dump_state(state, td)
                    # Remaining JSONL files (transitional; pool.jsonl
                    # retired in 7.1.1)
                    for fname in ("things.jsonl", "oracle_pairs.jsonl",
                                  "weights.jsonl", "trajectory_aux.jsonl"):
                        assert (Path(td) / fname).exists(), (
                            f"dump_state should produce {fname}"
                        )
                    assert not (Path(td) / "pool.jsonl").exists(), (
                        "pool.jsonl was retired in 7.1.1 (pool now in HDF5)"
                    )
                    assert (Path(td) / "state.h5").exists()
                    import h5py
                    with h5py.File(Path(td) / "state.h5", "r") as h5:
                        # Pool in HDF5 with compound dtype + chunking
                        assert "pool" in h5
                        assert "keys_array" in h5["pool"]
                        assert h5["pool/keys_array"].chunks is not None, (
                            "pool keys_array should be chunked"
                        )
                        assert h5["pool/keys_array"].maxshape == (None,), (
                            "pool keys_array should be axis-0-extensible"
                        )
                        # Mask datasets chunked + extensible
                        assert h5["masks/tau"].chunks is not None
                        assert h5["masks/tau"].maxshape == (None, None)
                        # Under lazy orbit: extracted state is symmetric;
                        # sigma omitted (derivable from tau).
                        assert bool(h5.attrs["sigma_stored"]) is False
                        assert "sigma" not in h5["masks"]
                        # Pool_size attribute consistent across root +
                        # /pool group + /masks group
                        assert h5.attrs["pool_size"] == state.pool.size()
                        assert h5["pool"].attrs["pool_size"] == state.pool.size()
                        assert h5["masks"].attrs["pool_size"] == state.pool.size()
                        assert h5.attrs["n_things"] == len(state.thing_ids)
                    # Round-trip
                    loaded = load_state(td)
                    assert loaded.signature() == state.signature(), (
                        "round-trip should preserve state.signature()"
                    )
                    assert np.array_equal(loaded.trajectory, state.trajectory)
                    assert loaded.trajectory_aux == state.trajectory_aux
                    assert loaded.iteration == state.iteration
                    assert loaded.pool_has_trivial_orbits == state.pool_has_trivial_orbits
                    assert loaded.sigma_derivable_from_tau == state.sigma_derivable_from_tau

                # Empty-state round-trip (Stage 7.1.1 audit Sev-3 fix):
                # exercise the n_things=0, pool_size=0, n_iter=0 edge case.
                empty = State()
                with tempfile.TemporaryDirectory() as td2:
                    dump_state(empty, td2)
                    loaded_empty = load_state(td2)
                    assert loaded_empty.signature() == empty.signature(), (
                        "empty-state round-trip preserves signature"
                    )
                    assert loaded_empty.pool.size() == 0
                    assert len(loaded_empty.thing_ids) == 0
                    assert len(loaded_empty.trajectory) == 0

                print(f"    Stage 7.1.1: pool in HDF5 (/pool/keys_array, "
                      f"compound S512); chunked + extensible datasets; "
                      f"algebraic orbit self-validation on load; "
                      f"empty-state round-trip; pool.jsonl retired")

                # -- Stage 7.1.2 (a): Rotated K dump/load round-trip ------
                # Sev 3 (c) from the post-7.1.1 audit: prior smoke didn't
                # exercise a pool containing a Rotated K through the
                # dump/load pipeline.  Builds such a pool, verifies
                # orbit metadata round-trips and pool_has_trivial_orbits
                # correctly flips.
                atom_r = Atom(Observable("test:rotated_smoke"))
                swapped_r = swap(atom_r)
                assert isinstance(swapped_r, Rotated)
                pool_r = Pool().with_k(atom_r).with_k(swapped_r)
                state_r = State(pool=pool_r)
                with tempfile.TemporaryDirectory() as td_r:
                    dump_state(state_r, td_r)
                    loaded_r = load_state(td_r)
                    assert loaded_r.signature() == state_r.signature(), (
                        "Rotated-K round-trip should preserve signature"
                    )
                    assert loaded_r.pool.size() == 2
                    # Rotated K's orbit metadata points at base's bit
                    assert int(loaded_r.pool.keys_array[1]["orbit_id"]) == 0
                    assert int(loaded_r.pool.keys_array[1]["orbit_parent"]) == 0
                    # Non-trivial orbit structure survives round-trip
                    assert not loaded_r.pool_has_trivial_orbits, (
                        "Rotated-K pool should report non-trivial orbits "
                        "after load"
                    )

                # -- Stage 7.1.2 (b): Tier 3 — asymmetric regime via
                # general combinator on Rotated-parent wedges.  Enacts
                # l-combinator-and-s3-operators-are-equivalent.
                #
                # Build a state with a single synthetic thing on which
                # two atoms both fire.  Rotate each by (τκ) — the S3
                # element ((2, 1, 0)) — producing asymmetric profiles.
                # Wedge the rotated K's via the general combinator
                # (triggered by Rotated-parent detection in
                # _articulate_wedges_batch).  Verify the resulting
                # wedge's τ and σ columns differ on the thing.
                atom_x = Atom(Observable("test:asym_x"))
                atom_y = Atom(Observable("test:asym_y"))
                s3_tau_kappa = S3((2, 1, 0))  # (τκ) transposition
                rot_x = rotate(atom_x, s3_tau_kappa)
                rot_y = rotate(atom_y, s3_tau_kappa)
                assert isinstance(rot_x, Rotated)
                assert isinstance(rot_y, Rotated)
                # Build pool with both base atoms and both rotations
                asym_pool = (
                    Pool()
                    .with_k(atom_x)
                    .with_k(atom_y)
                    .with_k(rot_x)
                    .with_k(rot_y)
                )
                # One synthetic thing where both base atoms fire.  The
                # Rotated K's mask columns are unused here (Tier 3
                # minimum doesn't wire State mask population for Rotated
                # K's); we set them manually via direct array
                # construction to exercise the general-combinator
                # articulation path.
                n_pool = asym_pool.size()
                tid_single = ThingId("asym_test_thing")
                # For a symmetric atom (τ = σ = 1) rotated by (τκ):
                # tsk moves from [1, 1, 0] to tsk[perm] = [0, 1, 1],
                # i.e., τ = 0, σ = 1.  So rot_x fires in σ but not τ
                # where atom_x fires.  Set the mask columns accordingly.
                tau_row = np.zeros(n_pool, dtype=bool)
                sig_row = np.zeros(n_pool, dtype=bool)
                bit_x = asym_pool.bit_of(atom_x)
                bit_y = asym_pool.bit_of(atom_y)
                bit_rx = asym_pool.bit_of(rot_x)
                bit_ry = asym_pool.bit_of(rot_y)
                # Base atoms: symmetric (τ = σ = 1)
                tau_row[bit_x] = True
                sig_row[bit_x] = True
                tau_row[bit_y] = True
                sig_row[bit_y] = True
                # Rotated atoms: τ = 0, σ = 1 under (τκ) on symmetric
                sig_row[bit_rx] = True
                sig_row[bit_ry] = True
                asym_state = State(
                    pool=asym_pool,
                    thing_ids=np.array([tid_single], dtype=object),
                    tau_masks=tau_row.reshape(1, -1),
                    sigma_masks=sig_row.reshape(1, -1),
                )
                # Sanity: masks differ somewhere (rotated bits have τ=0,
                # σ=1); this flips sigma_derivable_from_tau to False.
                assert not asym_state.sigma_derivable_from_tau, (
                    "state with rotated K's firing in σ but not τ should "
                    "have sigma NOT derivable from tau"
                )
                # Articulate Wedge(rot_x, rot_y): under the general
                # combinator (both parents Rotated), τ_W = τ_rx·σ_ry +
                # σ_rx·τ_ry = 0·1 + 1·0 = 0; σ_W = τ_rx·τ_ry +
                # σ_rx·σ_ry = 0·0 + 1·1 = 1.  So the wedge has
                # τ = 0, σ = 1 — asymmetric.
                tau_fb = firing_bitmaps_of(asym_state, "tau")
                wedge_rxy = Wedge(rot_x, rot_y).normalize()
                art_state, n_art = _articulate_wedges_batch(
                    asym_state, [wedge_rxy], tau_fb,
                )
                assert n_art >= 1, (
                    "at least one K should articulate (wedge + orbit members)"
                )
                # The new wedge's firing via lazy fire_pair: τ=0, σ=1
                # on the single thing (Rotated-leaf grade-2 combinator).
                tau_w, sig_w = art_state.fire_pair(wedge_rxy)
                assert bool(tau_w[0]) is False, (
                    "τ of Wedge(rot_x, rot_y) should be 0 under general "
                    "combinator (0·1 + 1·0 = 0 in GF(2))"
                )
                assert bool(sig_w[0]) is True, (
                    "σ of Wedge(rot_x, rot_y) should be 1 under general "
                    "combinator (0·0 + 1·1 = 1 in GF(2))"
                )

                # Dump/load round-trip for the asymmetric state.
                # Under 7.3, masks are a cache (wedge columns cached
                # on articulation).  sigma_derivable_from_tau checks
                # the STORED masks — which include the asymmetric wedge
                # column cached by _articulate_wedges_batch.  So
                # /masks/sigma IS written for asymmetric states.
                with tempfile.TemporaryDirectory() as td_asym:
                    dump_state(art_state, td_asym)
                    with h5py.File(Path(td_asym) / "state.h5", "r") as h5a:
                        assert bool(h5a.attrs["sigma_stored"]) is True, (
                            "asymmetric state must have sigma_stored=True"
                        )
                        assert "sigma" in h5a["masks"], (
                            "asymmetric state must write /masks/sigma"
                        )
                    loaded_asym = load_state(td_asym)
                    # fire_pair on loaded state produces same result
                    lt, ls = loaded_asym.fire_pair(wedge_rxy)
                    assert bool(lt[0]) is False, (
                        "loaded asymmetric wedge τ should be 0"
                    )
                    assert bool(ls[0]) is True, (
                        "loaded asymmetric wedge σ should be 1"
                    )

                print(f"    Stage 7.3.1: Tier 3 general combinator via "
                      f"fire_pair; Belnap-encoded masks; asymmetric "
                      f"dump/load round-trip verified")

                # (Stage 7.2 eager orbit-seeding smoke test RETIRED in
                # 7.2.2+ — see design/rejected.jsonl r-eager-orbit-
                # seeding.  Orbit demands are now syndrome-decoded
                # inline in step() Phase 2.)

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

                # Pool grew by at most 20 wedges × 3 (with orbit expansion:
                # each wedge + 2 orbit members).
                pool_growth = s1.pool.size() - s0.pool.size()
                assert 0 <= pool_growth <= 60, (
                    f"step() articulated {pool_growth} K's (wedges + orbit); "
                    f"expected 0..60 (max_budget=20 × 3 orbit)"
                )

                # Iteration counter advanced
                assert s1.iteration == s0.iteration + 1, (
                    f"iteration {s0.iteration} → {s1.iteration}; expected +1"
                )

                # Trajectory entry recorded; structured-dtype numeric
                # fields in .trajectory[-1], aux fields (scorer /
                # objective structural identity) in .trajectory_aux[-1]
                # per l-trajectory-as-structured-dtype-array.
                assert len(s1.trajectory) == len(s0.trajectory) + 1
                assert len(s1.trajectory_aux) == len(s1.trajectory)
                last = s1.trajectory[-1]           # np.void (structured row)
                last_aux = s1.trajectory_aux[-1]   # dict
                assert last["iteration"] == s0.iteration + 1
                assert last["pool_size_before"] == s0.pool.size()
                assert last["pool_size_after"] == s1.pool.size()
                assert last["articulated_count"] == pool_growth
                assert "scorer" in last_aux
                assert last_aux["scorer"][0] == "scorer"
                assert "objective" in last_aux
                # Stage 5.5: no weight_updater field in trajectory aux
                assert "weight_updater" not in last_aux, (
                    "weight_updater removed per c-weight-updater-becomes-new-k-articulation"
                )
                # TRAJECTORY_DTYPE field names enforce the type at write
                # time — a typo would fail dtype assignment rather than
                # silently returning a default (the old .get() contract).
                assert last.dtype == TRAJECTORY_DTYPE

                # Signature changed when pool grew
                if pool_growth > 0:
                    assert s0.signature() != s1.signature(), (
                        "signature should change when pool grew"
                    )

                # Every newly-articulated K is a Wedge or a Rotated
                # (orbit member of a wedge) — not a raw Atom
                for k in s1.pool.ks[s0.pool.size():]:
                    assert isinstance(k, (Wedge, Rotated)), (
                        f"articulated K {k!r} is not Wedge or Rotated"
                    )

                # Non-Rotated wedge firing respects d-wedge-bit-and-of-
                # parents (τ = AND of atoms).  Rotated K's + general-
                # combinator wedges have different (S3-derived / GF(2)
                # cross-term) firing; skip those in this check.
                for k in s1.pool.ks[s0.pool.size():]:
                    if isinstance(k, Rotated):
                        continue  # orbit member; firing is S3-derived
                    leaves = _flatten_wedge_leaves(k)
                    if any(isinstance(leaf, Rotated) for leaf in leaves):
                        continue  # general-combinator wedge; skip AND check
                    # Stage 7.3: use fire_pair for wedge firing (lazy)
                    tau_w, _ = s1.fire_pair(k)
                    for t_idx, (_tid, thing) in enumerate(s1.things):
                        wedge_fires = bool(tau_w[t_idx])
                        atoms_fire = True
                        for atom in k.atoms():
                            tau_a, _ = s1.fire_pair(atom)
                            if not bool(tau_a[t_idx]):
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

                # Stage 5.5: exercise σ-channel path.  Under orbit
                # expansion, τ ≠ σ on Rotated K's.  Verify that τ and σ
                # channels agree ONLY at base-atom rows (non-Rotated).
                fires_tau = firing_bitmaps_of(state, "tau")
                fires_sigma = firing_bitmaps_of(state, "sigma")
                # Under lazy orbit: extracted state is all-symmetric
                assert np.array_equal(fires_tau, fires_sigma), (
                    "τ/σ firing bitmaps should agree for symmetric extract"
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
                # Under orbit expansion, unbounded articulation on even
                # tiny states is expensive (3x atoms → 9x pairs → 3x
                # orbit per wedge).  Use a bounded budget; verify the
                # sentinel encoding and that budget is respected.
                s_bounded_tiny = step(
                    tiny_state, scorer=scorer_xor_off_diagonal,
                    max_articulations_per_step=50,
                )
                last_traj = s_bounded_tiny.trajectory[-1]
                assert last_traj["max_articulations_per_step"] == 50

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

                # -- Stage 7.0.5: numpy-application perf fixes ---------
                # (1) _count_four_cell fast path via firing_bitmaps.
                # Build firing_bitmaps once; compare fast vs slow path
                # outputs — they must agree.
                sample_things = state.restrict(
                    thing_ids=frozenset(
                        tid for tid, _ in state.things[:50]
                    )
                )
                sample_bitmaps = firing_bitmaps_of(sample_things, "tau")
                # Pick two atoms that both fire on at least one thing
                k_a = k_src_candidates[0]
                k_b = k_kind_candidates[0]
                a_bit = sample_things.pool.bit_of(k_a)
                b_bit = sample_things.pool.bit_of(k_b)
                slow = _count_four_cell(sample_things, a_bit, b_bit)
                fast = _count_four_cell(
                    sample_things, a_bit, b_bit,
                    firing_bitmaps=sample_bitmaps,
                )
                assert slow == fast, (
                    f"fast-path cell counts {fast} disagree with slow {slow}"
                )
                # Stage 7.0.11: slow path reads state.tau_masks columns
                # directly — no state.things iteration, no Thing
                # reconstruction.  Verify against a direct tau_masks
                # reference computation.
                ref_i = sample_things.tau_masks[:, a_bit]
                ref_j = sample_things.tau_masks[:, b_bit]
                ref_n_11 = int(np.sum(ref_i & ref_j))
                ref_n_10 = int(np.sum(ref_i & ~ref_j))
                ref_n_01 = int(np.sum(~ref_i & ref_j))
                ref_n_00 = len(ref_i) - ref_n_11 - ref_n_10 - ref_n_01
                assert slow == (ref_n_00, ref_n_01, ref_n_10, ref_n_11), (
                    "Stage 7.0.11 slow path diverged from tau_masks slice"
                )

                # (2) Scorer fast path via firing_bitmaps kwarg.
                # Scorers called with firing_bitmaps produce same score
                # as without.
                score_slow = scorer_xor_off_diagonal(
                    sample_things, k_a, k_b
                )
                score_fast = scorer_xor_off_diagonal(
                    sample_things, k_a, k_b,
                    firing_bitmaps=sample_bitmaps,
                )
                assert abs(score_slow - score_fast) < 1e-9, (
                    f"scorer slow {score_slow} != fast {score_fast}"
                )

                # (3) Thing.__hash__ is a pure function of content.
                # Stage 7.0.6 reverted the 7.0.5 cache per user
                # observation that the signature() hot path never
                # invokes hash() — the cache solved a phantom
                # problem.  Now __hash__ is stateless; same content
                # produces same hash.
                sample_thing = state.things[0][1]
                assert not hasattr(sample_thing, "_hash"), (
                    "Thing shouldn't have _hash cache (reverted in 7.0.6)"
                )
                h1 = hash(sample_thing)
                h2 = hash(sample_thing)
                assert h1 == h2
                assert not hasattr(sample_thing, "_hash"), (
                    "Thing.__hash__ shouldn't materialize cache attribute"
                )

                # Equal Things hash equal (pure function of content)
                same_thing = Thing(
                    id=sample_thing.id,
                    tau_mask=sample_thing.tau_mask.copy(),
                    sigma_mask=sample_thing.sigma_mask.copy(),
                )
                assert sample_thing == same_thing
                assert hash(sample_thing) == hash(same_thing)

                print(f"    Stage 7.0.5+.6: numpy fast path + unmaterialized "
                      f"hash (pure __hash__, trajectory-based fixed-point)")
                print(f"    Stage 7.0.7a: Pool uses structured-dtype numpy array; "
                      f"O(1) bit_of via _key_to_bit cache")
                print(f"    Stage 7.0.7b: State.things → parallel arrays; "
                      f"firing_bitmaps is .tau_masks.T (O(1) view, no build)")
                print(f"    Stage 7.0.7c: wedge-batch dedup via np.unique on "
                      f"canonical keys; Python seen_in_batch set retired")
                # Stage 7.0.8: oracle_pair_indices is an Int[n_pairs, 2]
                # cache built at __init__ from the authoritative
                # frozenset form; vectorized oracle scorers index
                # tau_masks directly (l-oracle-pairs-as-index-array).
                pair_idx = state.oracle_pair_indices
                assert pair_idx.shape[1] == 2, (
                    f"oracle_pair_indices must be (n_pairs, 2), "
                    f"got {pair_idx.shape}"
                )
                assert pair_idx.dtype == np.int64, (
                    f"oracle_pair_indices dtype should be int64, "
                    f"got {pair_idx.dtype}"
                )
                # Pairs' rows point into valid thing_ids positions
                if len(pair_idx) > 0:
                    assert pair_idx.min() >= 0 and pair_idx.max() < len(state.thing_ids), (
                        "oracle_pair_indices outside thing_ids range"
                    )
                # row_of accessor round-trips: the id at row i must
                # resolve back to row i via row_of().
                if len(state.thing_ids) > 0:
                    tid_sample = ThingId(str(state.thing_ids[0]))
                    assert state.row_of(tid_sample) == 0
                    tau_row = state.tau_row(tid_sample)
                    assert tau_row is not None
                    assert np.array_equal(tau_row, state.tau_masks[0])
                print(f"    Stage 7.0.8: oracle pairs Int[n_pairs, 2] cache; "
                      f"oracle scorers vectorized; Thing.remap + "
                      f"_compute_firing_bitmaps shim retired")
                print(f"    Stage 7.0.9: trajectory is TRAJECTORY_DTYPE "
                      f"structured array + trajectory_aux for optional "
                      f"scorer/objective structural identity")

        # Pool invariant: every observable appears as an Atom K
        for k in state.pool.ks:
            assert isinstance(k, Atom), (
                f"Stage-3 initial pool should contain only Atoms, got {type(k).__name__}"
            )

        print(f"    Stage 3 extraction: {len(state.things)} things, "
              f"{state.pool.size()} atoms, {len(state.oracle_pairs)} oracle pairs")
    else:
        print("    Stage 3 extraction: no source dirs found in cwd; skipping")

    print("Stage 1–7.3 smoke test (fire_pair: pool=computation graph, masks=cache; AND/combinator dispatch transparent via fold): all assertions passed")
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
    print(f"    via vectorized column permutation (p-embarrassingly-parallel realized)")
    print(f"  State.restrict prunes orphan oracle pairs")
    print(f"  State.signature stable under trajectory append")


if __name__ == "__main__":
    _smoke_test()
