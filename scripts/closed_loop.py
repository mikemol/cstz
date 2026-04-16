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
from typing import Iterator, Tuple


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
    def key(self) -> str:
        """Stable string key for pool registration.

        Atoms: the verbatim observation string.
        Wedges: recursively-derived key from sorted parents
                (provides wedge-commutativity canonicalization).
        """
        ...

    @abstractmethod
    def normalize(self) -> "K":
        """Return a canonical representative in the K's extensional
        equivalence class (under wedge commutativity).  Idempotent."""
        ...

    @abstractmethod
    def atoms(self) -> frozenset[str]:
        """Set of all atomic observation strings appearing in this K
        (transitively, across wedge parents).  Atoms' own key; wedges'
        union of their parents' atoms.  Used for redundancy checks."""
        ...


@dataclass(frozen=True, eq=True)
class Atom(K):
    """Primitive observation K: a verbatim observable string.

    Under ``p-atoms-are-formal-tau-sigma-channels``, the atom carries
    NO framework-level commitment about what ``observable`` observes;
    it is a population choice made by the extractor.  By default
    atoms have τ = σ at grade 1, giving κ = 0, but the framework
    supports any population.
    """

    observable: str

    @property
    def grade(self) -> int:
        return 1

    def key(self) -> str:
        return f"atom:{self.observable}"

    def normalize(self) -> "Atom":
        return self  # atoms are already canonical

    def atoms(self) -> frozenset[str]:
        return frozenset({self.observable})


@dataclass(frozen=True, eq=True)
class Wedge(K):
    """Grade-(max(a.grade, b.grade) + 1) K built from two lower K's via ∧.

    Intensional equality distinguishes ``Wedge(a, b)`` from ``Wedge(b, a)``
    since they are structurally different dataclass instances.
    Extensional equality (wedge commutativity) is earned via
    ``normalize()`` which sorts the parents by their key, returning
    the canonical representative.
    """

    a: K
    b: K

    @property
    def grade(self) -> int:
        return max(self.a.grade, self.b.grade) + 1

    def key(self) -> str:
        # Canonical key = sorted pair of parent keys
        ka, kb = self.a.key(), self.b.key()
        lo, hi = (ka, kb) if ka <= kb else (kb, ka)
        return f"wedge({lo},{hi})"

    def normalize(self) -> "Wedge":
        na = self.a.normalize()
        nb = self.b.normalize()
        if na.key() <= nb.key():
            return Wedge(na, nb)
        return Wedge(nb, na)

    def atoms(self) -> frozenset[str]:
        return self.a.atoms() | self.b.atoms()


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
        target = k.key()
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
    """A pooled named declaration.  The ``source_path`` + ``line`` are
    informational; the framework makes no commitment that "source" is
    a distinguished axis (``p-source-is-a-k`` — source is just
    another K observable).

    ``tau_mask`` and ``sigma_mask`` are bitmaps over the Pool: bit i
    set iff the K at pool position i fires on this thing in the
    respective channel.  ``kappa_mask`` is derived as tau ^ sigma
    by construction (never stored).
    """

    id: str                  # unique across corpus, e.g. "agda:module:Foo.Bar"
    display: str             # human-readable name
    source_path: str = ""    # file path for reporting only
    line: int = 0            # source line for reporting only
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
    things: Tuple[Tuple[str, Thing], ...] = ()        # sorted-by-id for hashability
    oracle_pairs: frozenset = frozenset()             # frozenset[frozenset[str]]
    weights: Tuple[Tuple[str, float], ...] = ()       # sorted-by-key for hashability
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
        new = tuple(sorted(others + ((thing.id, thing),), key=lambda kv: kv[0]))
        return State(
            pool=self.pool,
            things=new,
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

    def with_weight(self, k_key: str, w: float) -> "State":
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
        """Union two states.  Associative and commutative up to:
        - pool index reassignment (merged pool may index K's in a
          different order than either input; Things' bitmaps must be
          remapped if their Pool differs from the merged Pool);
        - weight collision: same-key weights average;
        - oracle pairs union;
        - trajectory concatenation (non-commutative; order-preserving
          via iteration counter).

        In this Stage-2 implementation we assume identical pools in
        both inputs — enforced by an assertion.  Cross-pool merge
        (which requires bitmap remapping) is Stage 10 concern.
        """
        # Pool merge (may reassign indices if different)
        merged_pool = self.pool.merge(other.pool)
        if merged_pool.keys != self.pool.keys or merged_pool.keys != other.pool.keys:
            # Cross-pool merge requires bitmap remapping; deferred.
            # For Stage 2, reject unless one is a prefix of the other.
            if not (self.pool.keys == merged_pool.keys[: len(self.pool.keys)]
                    and other.pool.keys == merged_pool.keys[: len(other.pool.keys)]):
                raise NotImplementedError(
                    "cross-pool merge with non-prefix divergence is Stage 10"
                )

        # Things: union by id; collision requires identical Thing (no bitmap remap yet)
        things_self = dict(self.things)
        things_other = dict(other.things)
        combined: dict = {}
        for tid in set(things_self) | set(things_other):
            if tid in things_self and tid in things_other:
                if things_self[tid] != things_other[tid]:
                    raise ValueError(f"thing id {tid!r} has diverging content across states")
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
        thing_ids: frozenset[str] | None = None,
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
    a = Atom("module")
    b = Atom("function")
    assert a.grade == 1 and b.grade == 1
    w = Wedge(a, b)
    assert w.grade == 2

    # Wedge commutativity: normalize sorts parents
    w_ab = Wedge(a, b)
    w_ba = Wedge(b, a)
    assert w_ab != w_ba  # intensionally distinct
    assert w_ab.normalize() == w_ba.normalize(), "wedge normalize not canonical"

    # Key stability
    assert w_ab.key() == w_ba.key(), "wedge key should be commutative-invariant"

    # Grade of nested wedges
    c = Atom("expr")
    w2 = Wedge(w, c)
    assert w2.grade == 3
    w3 = Wedge(c, w)
    assert w3.grade == 3

    # Atoms: union transitivity
    assert w2.atoms() == frozenset({"module", "function", "expr"})

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

    # Thing: κ_mask = τ_mask ⊕ σ_mask
    t = Thing(id="x", display="x", tau_mask=0b1010, sigma_mask=0b1100)
    assert t.kappa_mask == 0b0110

    # tausigma_at reads correctly
    t2 = Thing(id="y", display="y", tau_mask=0b101, sigma_mask=0b011)
    # Pool with 3 atoms a, b, c at bit indices 0, 1, 2
    pool = Pool().with_k(Atom("k0")).with_k(Atom("k1")).with_k(Atom("k2"))
    ts_at_0 = t2.tausigma_at(pool, Atom("k0"))
    assert ts_at_0.tau == 1 and ts_at_0.sigma == 1 and ts_at_0.kappa == 0
    ts_at_1 = t2.tausigma_at(pool, Atom("k1"))
    assert ts_at_1.tau == 0 and ts_at_1.sigma == 1 and ts_at_1.kappa == 1
    ts_at_2 = t2.tausigma_at(pool, Atom("k2"))
    assert ts_at_2.tau == 1 and ts_at_2.sigma == 0 and ts_at_2.kappa == 1

    # -- Stage 2: State merge / restrict / signature ------------------------

    # Two states with disjoint things, shared pool prefix
    pool_a = Pool().with_k(Atom("k0")).with_k(Atom("k1"))
    t1 = Thing(id="A", display="A", tau_mask=0b01, sigma_mask=0b01)
    t2 = Thing(id="B", display="B", tau_mask=0b10, sigma_mask=0b11)
    s1 = State(pool=pool_a, things=(("A", t1),), weights=(("atom:k0", 1.5),))

    # Second state uses an extended pool (prefix-compatible)
    pool_b = pool_a.with_k(Atom("k2"))
    t3 = Thing(id="C", display="C", tau_mask=0b100, sigma_mask=0b000)
    s2 = State(
        pool=pool_b,
        things=(("B", t2), ("C", t3)),
        oracle_pairs=frozenset({frozenset({"A", "B"})}),
        weights=(("atom:k1", 2.0),),
    )

    # Merge: pool unions to the extended form; things union; weights union
    m = s1.merge(s2)
    assert m.pool.size() == 3, f"merged pool size {m.pool.size()}"
    assert len(m.things) == 3, f"merged things count {len(m.things)}"
    assert frozenset({"A", "B"}) in m.oracle_pairs
    assert m.weight_of(Atom("k0")) == 1.5
    assert m.weight_of(Atom("k1")) == 2.0

    # Merge idempotent
    assert m.merge(m).signature() == m.signature(), "merge not idempotent"

    # Merge associative (order-preserving on trajectory only; identity elsewhere)
    s3 = State(pool=pool_b, things=(("D", Thing(id="D", display="D")),))
    left = (s1.merge(s2)).merge(s3)
    right = s1.merge(s2.merge(s3))
    assert left.signature() == right.signature(), "merge not associative"

    # Weight collision: averaged on merge
    sA = State(pool=pool_a, weights=(("atom:k0", 1.0),))
    sB = State(pool=pool_a, weights=(("atom:k0", 3.0),))
    sAB = sA.merge(sB)
    assert sAB.weight_of(Atom("k0")) == 2.0, "weight collision not averaged"

    # Restrict: subset of things + pruned oracle
    restricted = m.restrict(thing_ids=frozenset({"A"}))
    assert len(restricted.things) == 1
    assert len(restricted.oracle_pairs) == 0, "oracle with absent endpoint not pruned"

    # Restrict preserving oracle
    restricted2 = m.restrict(thing_ids=frozenset({"A", "B"}))
    assert len(restricted2.things) == 2
    assert frozenset({"A", "B"}) in restricted2.oracle_pairs

    # Signature changes when pool grows
    sig_before = s1.signature()
    s1_ext = s1.with_pool(pool_b)
    sig_after = s1_ext.signature()
    assert sig_before != sig_after, "signature should change when pool changes"

    # Appending trajectory advances iteration without changing signature
    s1_traj = s1.appending_trajectory({"note": "hello"})
    assert s1_traj.signature() == s1.signature(), (
        "trajectory append should not affect signature"
    )
    assert s1_traj.iteration == s1.iteration + 1

    print("Stage 1 + 2 smoke test: all assertions passed")
    print(f"  TauSigma invariant OK for all 4 cases × 6 S3 elements")
    print(f"  Wedge commutativity canonicalized via normalize()")
    print(f"  Pool append/merge idempotent; bit indices stable")
    print(f"  κ = τ ⊕ σ preserved by Thing.kappa_mask and TauSigma.kappa")
    print(f"  State.merge associative, idempotent; weights averaged on collision")
    print(f"  State.restrict prunes orphan oracle pairs")
    print(f"  State.signature stable under trajectory append")


if __name__ == "__main__":
    _smoke_test()
