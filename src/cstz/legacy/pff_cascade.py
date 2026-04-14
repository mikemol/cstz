"""PFF cascade engine — native operational layer over pff.Document.

This module is the **parallel** PFF implementation of the cascade.
It exists alongside the legacy ``cstz.core`` stack (which remains the
metamathematical reference proven against ``inference.agda``) and
implements the same mathematical content in PFF/RHPF vocabulary
directly, with no dependence on ``core.py``.

Architecture:

    Layer 1   pff.py             — pure dataclasses + SHACL validators
    Layer 2   pff_cascade.py     — native cascade engine                ← here
    Layer 3   pff_python_classifier.py (planned), agda_synth extensions

Vocabulary mapping (PFF normative):

    add_observation                ↔  POST /documents (one observation =
                                       one Addr0 with one Segment)
    glue closure (path1)           ↔  Addr1 with ctor=glue, computed by
                                       union-find over Addr0 ids
    coh closure (path2)            ↔  Addr2 with ctor=coh, computed by
                                       union-find over Addr1 ids
    Chart.kind ∈ {sigma, tau}      ↔  the κ = σ ⊎_τ σ coproduct
                                       (reading (b) — implementation primary)
    Pair.role ∈ {principal, aux}   ↔  per-pair canonical-vs-auxiliary
                                       discriminator within a chart;
                                       also the basis for the reading-(a)
                                       projection (`as_role_coproduct`)

The engine is **independent** of core.SPPF.  It does not import from
``core``, does not use ``Fiber`` / ``FiberClass``, and operates on
PFF identifiers (strings) directly throughout.  The legacy three-fiber
state machinery is recoverable from a Document only as a *derived
view* (see ``role_coproduct_view``).

Streaming cascade semantics
---------------------------

When an observation is added, it is keyed by:

    sigma_key = (sigma_chart_id, canonical_child_addr0_ids)

If another observation already exists with the same sigma_key but a
different aux (τ-side) chart, that is the η-coincidence: two
observations have the same syntactic shape but different dependent
type.  The engine emits an Addr1 with ``ctor=glue`` between them and
unions their addr0 ids in the path1 union-find.

After every glue, the engine re-canonicalizes structural keys whose
children just moved.  If two re-canonicalized keys collide, that is a
cascading glue.  The cascade runs to fixed point.

The Document remains well-formed (``document.receipt().wfStatus ==
'clean'``) at every step of the cascade.

Path2 (coh) closure
-------------------

The path2 / coh layer is **user-initiated** in this implementation.
The streaming cascade does not auto-emit coh records.  Reasoning:

  - In the cascade as currently designed, ``glue()`` is idempotent
    (a second glue between addr0s already in the same path1 class is
    a no-op), and the cascade itself skips already-merged pairs.  So
    two distinct Addr1s with the same canonical endpoints never arise
    from streaming alone.
  - Coh becomes meaningful when the user explicitly records two
    different proofs of the same equality (two Addr1s with the same
    src/dst that arose from different premise sets) and wants to
    witness their coherence.

Use ``engine.coh(addr1_a, addr1_b)`` to record a path2 witness
between two existing Addr1s.  The engine maintains a path2 union-find
over Addr1 ids so coh is itself idempotent.
"""

from __future__ import annotations

from collections import defaultdict
from typing import (
    Any,
    Dict,
    FrozenSet,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from .pff import (
    Addr0,
    Addr1,
    Addr2,
    Cell,
    Chart,
    Document,
    Pair,
    Patch,
    PERSPECTIVE_KAPPA,
    PERSPECTIVE_SIGMA,
    PERSPECTIVE_TAU,
    Rank,
    Segment,
    Step,
    morphism_term,
    sigma_key,
)


# ── Union-find ──────────────────────────────────────────────────────
#
# A weighted union-find with path compression, parameterized over the
# element type.  PFF cascade uses two instances of this structure:
# one over Addr0 ids (for the glue/path1 closure) and one over Addr1
# ids (for the coh/path2 closure).
#
# It is intentionally a fresh implementation rather than an import
# from ``core.py`` so this module has zero dependence on the legacy
# stack.


class _UnionFind:
    """Weighted union-find with path compression over hashable elements."""

    __slots__ = ("_parent", "_rank")

    def __init__(self) -> None:
        self._parent: Dict[Any, Any] = {}
        self._rank: Dict[Any, int] = {}

    def make(self, x: Any) -> None:
        if x not in self._parent:
            self._parent[x] = x
            self._rank[x] = 0

    def __contains__(self, x: object) -> bool:
        return x in self._parent

    def find(self, x: Any) -> Any:
        # Two-pass: find the root, then compress.
        r = x
        while self._parent[r] != r:
            r = self._parent[r]
        while self._parent[x] != r:
            self._parent[x], x = r, self._parent[x]
        return r

    def union(self, a: Any, b: Any) -> Any:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return ra
        if self._rank[ra] < self._rank[rb]:
            ra, rb = rb, ra
        self._parent[rb] = ra
        if self._rank[ra] == self._rank[rb]:
            self._rank[ra] += 1
        return ra

    def __iter__(self) -> Iterator[Any]:
        return iter(self._parent)

    def __len__(self) -> int:
        return len(self._parent)


# ── Fiber — perspective-indexed equivalence-class registry ──────────
#
# Pass 2 of Step 1.5.1 ports the three-Fiber structure from
# ``src/cstz/core.py`` (the legacy SPPF reference) into the PFF
# cascade engine.  Each Fiber is a registry of equivalence classes
# under one perspective: cells with the same `sigma_key` under that
# perspective collapse into the same FiberClass.
#
# **Pass 2 scope is additive and passive:** the Fibers accumulate
# cells alongside the existing Step 1.5 ``_uf`` and
# ``_morphism_signature_index`` machinery, but they do not yet drive
# emission decisions.  The existing σ-perspective hash-cons (in
# ``_emit_glue`` and ``add_observation``) remains the load-bearing
# path; the Fibers are populated as a parallel observation so Pass
# 3's ``Document.hom_set`` query can read from them.  Pass 2 thus
# preserves byte-equivalence with Step 1.5 by construction.
#
# Reading A labeling (matching ``core.py``):
#   - σ-fiber (finest) — full structural fingerprint via
#     ``PERSPECTIVE_SIGMA``.  Two cells in the same FiberClass have
#     the same sort, segments, ctor, endpoints, and premises.
#   - τ-fiber (middle) — drops segments and premises.  Two cells
#     in the same FiberClass have the same sort, ctor, and endpoints.
#   - κ-fiber (coarsest) — drops ctor and premises.  Two cells in
#     the same FiberClass have the same sort and endpoints (any
#     morphism between the same pair of objects, regardless of
#     constructor).
#
# See plan-file conception matrix cells:
#   - CoreFiberIsParallelUF — the spatial-basis implementation
#     choice (one mutable UF per Fiber).
#   - SpatialAndTemporalAreBasisChange — the basis-change reframe
#     of the persistent-vs-parallel question.
#   - WedgeIsNDFixedPoint — the wedge product σ ∧ τ ∧ κ as the
#     N-D fixed point.


class _FiberClass:
    """A single equivalence class in one Fiber.

    The class is identified by its ``signature`` (the perspective-
    parameterized sigma_key tuple) and tracks the set of cell ids
    that share that signature.  ``representative`` is the
    first-ingested cell id (used for canonical-id queries).
    """

    __slots__ = ("signature", "representative", "members")

    def __init__(
        self,
        signature: Tuple[Any, ...],
        representative: str,
    ) -> None:
        self.signature: Tuple[Any, ...] = signature
        self.representative: str = representative
        self.members: Set[str] = {representative}

    def add(self, cell_id: str) -> None:
        """Add a cell id to this class.  Idempotent."""
        self.members.add(cell_id)

    def __repr__(self) -> str:
        return (
            f"_FiberClass(rep={self.representative!r}, "
            f"size={len(self.members)})"
        )


class _Fiber:
    """One perspective's equivalence-class registry over cell ids.

    Mirrors ``core.py:Fiber`` adapted to PFF cell ids (which are
    strings, not opaque ints).  Each Fiber owns:

      - ``perspective`` — the discriminator frozenset that defines
        which questions this Fiber asks about a cell
      - ``classes`` — signature → _FiberClass map
      - ``class_of`` — cell id → signature reverse index
      - ``uf`` — a mutable union-find over signatures, used by
        Pass 4+ if the cascade ever grows the ability to merge
        FiberClasses (for example, when an η-cascade discovers
        that two τ-keyed classes should be unified).  In Pass 2,
        the union-find is created but never unioned; this is the
        spatial-basis-only realization.

    Pass 2 instantiates one ``_Fiber`` per named perspective on
    the engine and ``observe()``s every newly-emitted cell into
    all three Fibers.  The Fibers are read-only from the cascade's
    emission logic; only ``observe()`` mutates them.
    """

    __slots__ = ("name", "perspective", "classes", "class_of", "uf")

    def __init__(self, name: str, perspective: str) -> None:
        self.name: str = name
        self.perspective: str = perspective
        self.classes: Dict[Tuple[Any, ...], _FiberClass] = {}
        self.class_of: Dict[str, Tuple[Any, ...]] = {}
        self.uf: _UnionFind = _UnionFind()

    def observe(self, cell: Cell) -> _FiberClass:
        """Register a cell in this Fiber under its perspective.

        Computes ``sigma_key(cell, perspective=self.perspective)``,
        looks up or creates the matching _FiberClass, and adds
        the cell's id to its members.  Returns the _FiberClass
        the cell landed in.

        Idempotent: observing the same cell twice is a no-op
        because ``_FiberClass.add`` is set-membership.
        """
        signature = sigma_key(cell, perspective=self.perspective)
        fc = self.classes.get(signature)
        if fc is None:
            fc = _FiberClass(signature=signature, representative=cell.id)
            self.classes[signature] = fc
            self.uf.make(signature)
        fc.add(cell.id)
        self.class_of[cell.id] = signature
        return fc

    def class_for(self, cell_id: str) -> Optional[_FiberClass]:
        """Return the _FiberClass containing this cell id, or None."""
        sig = self.class_of.get(cell_id)
        if sig is None:
            return None
        return self.classes[sig]

    def __len__(self) -> int:
        return len(self.classes)

    def __repr__(self) -> str:
        return (
            f"_Fiber({self.name!r}, "
            f"{len(self.classes)} classes, "
            f"{len(self.class_of)} cells)"
        )


# ── Helpers for hashable Pair signatures ────────────────────────────


def _payload_signature(payload: Any) -> Any:
    """Best-effort hashable signature for a chart payload."""
    if payload is None:
        return None
    if isinstance(payload, (str, int, float, bool, tuple)):
        return payload
    if isinstance(payload, dict):
        return tuple(sorted(
            (str(k), _payload_signature(v)) for k, v in payload.items()
        ))
    if isinstance(payload, (list, set, frozenset)):
        return tuple(_payload_signature(v) for v in payload)
    return repr(payload)


# ── Result types ────────────────────────────────────────────────────


class GlueResult:
    """Result of an explicit glue() call.

    Attributes:
        addr1: the newly minted Addr1, or None if the endpoints were
               already in the same path1 class
        cascade_addr1s: any additional Addr1s minted by the recursive
               cascade triggered by this glue
        was_noop: True if the original endpoints were already glued
    """

    __slots__ = ("addr1", "cascade_addr1s", "was_noop")

    def __init__(
        self,
        addr1: Optional[Addr1],
        cascade_addr1s: Optional[List[Addr1]] = None,
    ) -> None:
        self.addr1 = addr1
        self.cascade_addr1s = list(cascade_addr1s or [])
        self.was_noop = addr1 is None

    @property
    def all_addr1s(self) -> List[Addr1]:
        out: List[Addr1] = []
        if self.addr1 is not None:
            out.append(self.addr1)
        out.extend(self.cascade_addr1s)
        return out


# ── PFFCascadeEngine ────────────────────────────────────────────────


class PFFCascadeEngine:
    """Native PFF cascade engine over a pff.Document.

    Owns:
      - a ``pff.Document`` (the authoritative store)
      - a path1 union-find over Addr0 ids
      - a path2 union-find over Addr1 ids
      - a chart registry (dedupe by signature)
      - a sigma-key index for streaming glue detection
      - a glue index for streaming coh detection

    The engine is the *only* path through which mutations should reach
    the Document.  Direct mutations to ``self.document.addresses0``
    etc. will silently desynchronize the cascade indices.

    Public API:
      - ensure_rank(...) / ensure_patch(...) / ensure_chart(...) —
        idempotent record minting
      - add_observation(...) — the principal ingest entry point;
        emits one Addr0 + Segment + Pairs and runs the streaming
        glue + coh cascade
      - glue(src, dst, ...) — explicit path1 emission with cascade
      - coh(src, dst, ...) — explicit path2 emission
      - role_coproduct_view() — reading (a) projection of κ
    """

    DEFAULT_DOCUMENT_ID = "cstz-pff-doc"
    DEFAULT_RANK_LABEL = "ingest"
    DEFAULT_PATCH_LABEL = "cstz-pff-cascade"

    # ── Construction ────────────────────────────────────────────

    def __init__(self, document_id: Optional[str] = None) -> None:
        self.document: Document = Document(
            documentId=document_id or self.DEFAULT_DOCUMENT_ID,
        )

        # ── Unified union-find over Cell ids (HIT collapse) ──
        # Single _uf replaces the previous _addr0_uf / _addr1_uf
        # pair.  Cell ids are globally unique across ranks (the
        # engine mints "addr0-N", "addr1-N", "addr2-N" with disjoint
        # prefixes), so a single union-find keyed by id handles
        # both path1 and path2 closures without ambiguity.  The
        # previous two-union-find split was a bookkeeping
        # convenience, not a structural requirement.
        #
        # _addr0_uf / _addr1_uf are preserved as read-only property
        # aliases below for backward compat with any code that
        # inspected the engine's internals directly.
        self._uf: _UnionFind = _UnionFind()

        # ── Registries (signatures → records) ──
        # Records are stored directly so lookups never need a second
        # pass through the document.  Correct-by-construction: every
        # entry in a registry is also in the document by virtue of
        # both being appended together.
        self._chart_registry: Dict[Tuple[str, str, Any], Chart] = {}
        self._rank_by_ordinal: Dict[int, Rank] = {}
        self._patch_by_phase: Dict[Tuple[str, str], Patch] = {}
        self._addr0_signature_index: Dict[Tuple[Any, ...], Addr0] = {}
        # Hash-cons index for rank-1+ cells (morphisms).  Keyed by
        # the cell's sigma_key (computed via pff.sigma_key).  When
        # _emit_glue is called with endpoints that would produce a
        # duplicate cell, it returns the existing one from this
        # index instead of minting a new one.  This absorbs what
        # auto_coh_closure used to do post-hoc — morphism duplicates
        # can't be created in the first place.
        self._morphism_signature_index: Dict[Tuple[Any, ...], Any] = {}

        # ── Cascade indices ──
        # sigma_key = (sigma_chart_id, canonical_child_addr0_ids)
        # The set of addr0 ids that currently have this exact sigma key
        # AFTER chasing the path1 union-find on their children.
        self._addr0s_by_sigma_key: Dict[
            Tuple[str, Tuple[str, ...]], Set[str]
        ] = defaultdict(set)
        # Reverse index: which sigma_keys mention this addr0 as a child?
        # Used to seed the cascade worklist after a glue.
        self._sigma_keys_by_child: Dict[str, Set[Tuple[str, Tuple[str, ...]]]] = (
            defaultdict(set)
        )
        # Per-addr0 metadata
        self._addr0_sigma_key: Dict[str, Tuple[str, Tuple[str, ...]]] = {}
        self._addr0_tau_chart: Dict[str, str] = {}
        self._addr0_children: Dict[str, Tuple[str, ...]] = {}

        # ── Id counters ──
        self._next_id: Dict[str, int] = defaultdict(int)

        # ── Three-Fiber perspective lattice (Pass 2 of Step 1.5.1) ──
        # Pass 2 ports the legacy core.py three-Fiber structure into
        # the PFF cascade engine.  Each Fiber is a registry of
        # equivalence classes under one perspective; cells with the
        # same sigma_key under that perspective collapse into the
        # same FiberClass.
        #
        # **Pass 2 is additive and passive:** the Fibers accumulate
        # cells in parallel with the existing Step 1.5 _uf and
        # _morphism_signature_index machinery, but they do NOT yet
        # drive emission decisions.  The existing σ-perspective
        # hash-cons remains the load-bearing path; Pass 3 will
        # consume the Fibers via Document.hom_set queries.
        #
        # See plan-file conception matrix cells:
        #   - Step151IsAPort
        #   - CoreFiberIsParallelUF
        #   - WedgeIsNDFixedPoint
        self.sigma_fiber: _Fiber = _Fiber("sigma", PERSPECTIVE_SIGMA)
        self.tau_fiber: _Fiber = _Fiber("tau", PERSPECTIVE_TAU)
        self.kappa_fiber: _Fiber = _Fiber("kappa", PERSPECTIVE_KAPPA)

        # ── Three v2-aligned ports from core.py ──
        # The v2 conception matrix's "core.py walk" identified three
        # mechanisms in the legacy reference implementation that the
        # PFF stack lacked: residue tracking, dynamic cleavage Fibers,
        # and an eta-abstraction union-find.  These are independent of
        # the QIIT re-grounding and can ship under v1 vocabulary.  All
        # three are additive and passive: they create infrastructure
        # available to future callers without changing existing
        # emission decisions.

        # ── Eta-abstraction UF: substrate-level identity for named
        # bindings.  Mirrors core.py:_eta_uf and _eta_abstractions
        # ([core.py:173-174](../../github/cstz/src/cstz/core.py#L173)).
        # Initially empty; callers populate it via the eta_make /
        # eta_abstract / eta_union public methods.  Use case: tracking
        # that two analytical names refer to the same thing without
        # conflating them with the cell ids they appear in.
        self._eta_uf: _UnionFind = _UnionFind()
        self._eta_abstractions: Dict[str, str] = {}

        # ── Residue tracking: raw-endpoint witness preservation.
        # Mirrors core.py:_residue_sets ([core.py:179](../../github/cstz/src/cstz/core.py#L179)).
        # When _emit_glue and add_observation canonicalize endpoints
        # via _uf.find, the raw pre-canonical endpoints are lost from
        # the sigma_key.  These dicts preserve the raw forms keyed by
        # the chosen Cell id (canonical at insertion time).  Public
        # accessors addr0_residue / addr1_residue project through the
        # current _uf canonical map at query time, so unions after
        # insertion are reflected automatically without needing a
        # merge step.
        self._addr0_residue: Dict[str, Set[Tuple[str, ...]]] = defaultdict(set)
        self._addr1_residue: Dict[str, Set[Tuple[str, str]]] = defaultdict(set)

        # ── Dynamic cleavage Fibers: runtime-extensible perspective
        # lattice.  Mirrors core.py:_cleavage_fibers ([core.py:181](../../github/cstz/src/cstz/core.py#L181)).
        # The static σ/τ/κ trio above is augmented with a list of
        # additional Fibers added at runtime via add_cleavage_fiber.
        # When a new cleavage Fiber is added, every existing cell is
        # observed into it; subsequent emissions also flow into it via
        # _observe_into_fibers's loop.  This is the *infrastructure*
        # for dynamic cleavage; core.py's automatic triggering policy
        # (via κ-tag diversity in _process_cleavage) is NOT ported
        # because PFF lacks κ-tags in core.py's sense.  Callers may
        # use the infrastructure to add cleavage Fibers programmatically
        # for any custom perspective.
        self._cleavage_fibers: List[_Fiber] = []

    # ── Id minting ──────────────────────────────────────────────

    # ── Three-Fiber observation helper (Pass 2) ─────────────────

    def _observe_into_fibers(self, cell: Cell) -> None:
        """Register a cell in all three static Fibers under their
        respective perspectives, plus all dynamic cleavage Fibers
        currently in ``self._cleavage_fibers``.

        Pass 2: this is the *only* mutation point for the Fiber
        registries, called from each emission site exactly once
        per newly-minted cell.  The call is idempotent because
        ``_Fiber.observe`` uses set membership for class members,
        so re-observing an already-registered cell is a no-op.
        Hash-cons hits in ``_emit_glue`` and ``add_observation``
        return existing cells *before* this method is called, so
        the Fibers see each cell exactly once at first emission.

        v2 port: also observes the cell into every dynamic cleavage
        Fiber added via ``add_cleavage_fiber``.  The dynamic Fibers
        accumulate alongside the static trio.
        """
        self.sigma_fiber.observe(cell)
        self.tau_fiber.observe(cell)
        self.kappa_fiber.observe(cell)
        for fiber in self._cleavage_fibers:
            fiber.observe(cell)

    # ── v2 port: eta-abstraction union-find ─────────────────────
    #
    # Mirrors core.py's _eta_uf + _eta_abstractions mechanism.  An
    # *abstraction* is a named binding (string) that may be claimed
    # to be the canonical form of multiple raw names.  The eta UF
    # unifies abstraction names that turn out to refer to the same
    # underlying binding.  Use case: tracking that two analytical
    # names (e.g., two patch labels, two rank descriptors, two
    # external symbol references) are identified, without
    # conflating them with the Cell ids they appear in.
    #
    # All four methods are no-ops on the cascade's emission paths;
    # they exist as a parallel substrate-level identity tracker
    # that callers can populate as needed.

    def eta_make(self, name: str) -> None:
        """Register a name in the eta-abstraction union-find.

        Idempotent: calling ``eta_make("X")`` twice is a no-op
        the second time.  After ``eta_make("X")``, ``eta_find("X")``
        returns ``"X"``.
        """
        self._eta_uf.make(name)

    def eta_abstract(self, raw_name: str, abstract_name: str) -> None:
        """Record that ``raw_name`` is an instance of the named
        abstraction ``abstract_name``.

        After this call, ``eta_find(raw_name)`` returns the canonical
        form of ``abstract_name`` under the eta UF.  The abstraction
        target is registered in the UF if it isn't already.

        First-writer-wins: if ``raw_name`` is already mapped to a
        different abstraction, the existing mapping is preserved
        and the new call has no effect.  Callers that want to
        re-bind a raw name should ``eta_union`` the old and new
        abstraction names instead.
        """
        if raw_name in self._eta_abstractions:
            return
        self._eta_abstractions[raw_name] = abstract_name
        self._eta_uf.make(abstract_name)

    def eta_union(self, a: str, b: str) -> str:
        """Unify two abstraction names; return the canonical id.

        Both names are registered in the eta UF if they aren't
        already.  After this call, ``eta_find(a) == eta_find(b)``.
        """
        self._eta_uf.make(a)
        self._eta_uf.make(b)
        return self._eta_uf.union(a, b)

    def eta_find(self, name: str) -> str:
        """Resolve a name through the abstraction map and the
        eta UF.

        Walks ``_eta_abstractions`` once (raw → abstraction), then
        walks the eta UF to its canonical root.  If the name is
        neither an abstraction nor a registered UF element,
        returns the name unchanged.
        """
        target = self._eta_abstractions.get(name, name)
        if target in self._eta_uf:
            return self._eta_uf.find(target)
        return target

    # ── v2 port: residue tracking ───────────────────────────────
    #
    # Mirrors core.py's _residue_sets mechanism.  When the cascade
    # canonicalizes endpoints (via _uf.find) before computing
    # sigma_keys, the raw pre-canonical forms are lost.  Residue
    # tracking preserves them in a sidecar dict keyed by the chosen
    # Cell id.  Public accessors project through the current _uf
    # canonical map at query time, so unions that happen after
    # insertion are reflected automatically.

    def addr0_residue(self, addr0_id: str) -> FrozenSet[Tuple[str, ...]]:
        """Return all raw ``sigma_children`` tuples that produced
        any Addr0 in the same path1 class as ``addr0_id``.

        On a hash-cons hit (an observation that reuses an existing
        Addr0), the new caller's raw children tuple is added to
        the residue set so multiple distinct raw children that all
        canonicalize to the same Addr0 are preserved as evidence.

        Returns the union of residues across the entire path1
        class containing ``addr0_id``, computed by walking the
        residue dict and grouping by current canonical id.  This
        is O(N) per query in the size of the residue dict; it
        avoids needing a merge step at union time.

        Returns an empty frozenset if no residue is recorded for
        any Addr0 in the class.
        """
        if addr0_id not in self._uf:
            return frozenset(self._addr0_residue.get(addr0_id, set()))
        canonical = self._uf.find(addr0_id)
        out: Set[Tuple[str, ...]] = set()
        for aid, residue in self._addr0_residue.items():
            if aid in self._uf and self._uf.find(aid) == canonical:
                out |= residue
        return frozenset(out)

    def addr1_residue(self, addr1_id: str) -> FrozenSet[Tuple[str, str]]:
        """Return all raw ``(src, dst)`` pairs that produced any
        Addr1 in the same path2 class as ``addr1_id``.

        Mirrors :meth:`addr0_residue` for Addr1s.  On a hash-cons
        hit in ``_emit_glue``, the new caller's raw endpoints are
        added to the residue set even though no new Addr1 is
        minted.  Cross-Addr1 unions (from ``coh``) are reflected
        at query time via the canonical id projection.
        """
        if addr1_id not in self._uf:
            return frozenset(self._addr1_residue.get(addr1_id, set()))
        canonical = self._uf.find(addr1_id)
        out: Set[Tuple[str, str]] = set()
        for aid, residue in self._addr1_residue.items():
            if aid in self._uf and self._uf.find(aid) == canonical:
                out |= residue
        return frozenset(out)

    # ── v2 port: dynamic cleavage Fibers ────────────────────────
    #
    # Mirrors core.py's _cleavage_fibers list.  Adds a runtime
    # extension point to the static σ/τ/κ trio: callers can append
    # additional Fibers under custom perspectives, and every
    # existing and future cell is automatically observed into them.

    def add_cleavage_fiber(
        self,
        name: str,
        perspective: FrozenSet[str],
    ) -> _Fiber:
        """Append a new dynamic Fiber under ``perspective`` and
        observe every existing cell into it.

        Subsequent emissions (via ``add_observation``,
        ``_emit_glue``, ``coh``) will also observe new cells into
        this Fiber via ``_observe_into_fibers``.

        Returns the newly created ``_Fiber`` so the caller can
        immediately query its classes.

        Use case: at runtime, the caller decides that a particular
        sub-perspective is needed (e.g., a cleavage along a
        substrate-specific discriminator that the static σ/τ/κ
        constants don't capture).  ``add_cleavage_fiber`` makes
        the new perspective first-class without restarting the
        engine.
        """
        fiber = _Fiber(name, perspective)
        # Observe all existing cells into the new Fiber so it
        # starts in sync with the static trio.
        for cell in self.document.cells():
            fiber.observe(cell)
        self._cleavage_fibers.append(fiber)
        return fiber

    def cleavage_fibers(self) -> Tuple[_Fiber, ...]:
        """Return the current tuple of dynamic cleavage Fibers,
        in insertion order.

        The returned tuple is a snapshot — adding more Fibers via
        ``add_cleavage_fiber`` after the call will not affect the
        previously-returned tuple.
        """
        return tuple(self._cleavage_fibers)

    def _mint_id(self, prefix: str) -> str:
        n = self._next_id[prefix]
        self._next_id[prefix] = n + 1
        return f"{prefix}-{n}"

    # ── Rank / Patch / Chart minting (all idempotent) ───────────

    def ensure_rank(
        self,
        ordinal: int = 0,
        label: Optional[str] = None,
    ) -> Rank:
        """Return the Rank with this ordinal, minting it if absent."""
        existing = self._rank_by_ordinal.get(ordinal)
        if existing is not None:
            return existing
        rank = Rank(
            id=self._mint_id("rank"),
            ordinal=ordinal,
            label=label or self.DEFAULT_RANK_LABEL,
        )
        self.document.ranks.append(rank)
        self._rank_by_ordinal[ordinal] = rank
        return rank

    def ensure_patch(
        self,
        phase: str = "ingest",
        rank: Optional[Rank] = None,
        label: Optional[str] = None,
    ) -> Patch:
        """Return the Patch for this (rank, phase), minting it if absent."""
        if rank is None:
            rank = self.ensure_rank()
        key = (rank.id, phase)
        existing = self._patch_by_phase.get(key)
        if existing is not None:
            return existing
        patch = Patch(
            id=self._mint_id("patch"),
            rank=rank.id,
            phase=phase,
            label=label or self.DEFAULT_PATCH_LABEL,
        )
        self.document.patches.append(patch)
        self._patch_by_phase[key] = patch
        return patch

    def ensure_chart(
        self,
        kind: str,
        root: str,
        payload: Any = None,
        patch: Optional[Patch] = None,
    ) -> Chart:
        """Return the Chart with this (kind, root, payload), minting if absent.

        ``kind`` is the κ-coproduct discriminator (reading (b)): the
        canonical values are "sigma" (syntactic side) and "tau"
        (dependent-type side), but any string is accepted so the
        engine remains useful for other partitions of the chart space.
        """
        sig = (kind, root, _payload_signature(payload))
        existing = self._chart_registry.get(sig)
        if existing is not None:
            return existing
        chart = Chart(
            id=self._mint_id(f"chart-{kind}"),
            root=root,
            kind=kind,
            payload=payload,
            patch=patch.id if patch is not None else None,
        )
        self.document.charts.append(chart)
        self._chart_registry[sig] = chart
        return chart

    # ── Observation ingest ──────────────────────────────────────

    def add_observation(
        self,
        sigma_chart: Chart,
        tau_chart: Chart,
        sigma_children: Sequence[str] = (),
        tau_children: Sequence[str] = (),
        sort: Optional[str] = None,
        node_root: Optional[str] = None,
        rank: Optional[Rank] = None,
        patch: Optional[Patch] = None,
    ) -> Addr0:
        """Ingest one observation into the Document.

        An *observation* is a single source-level fact: a token, an
        AST node, a record, etc.  It is materialized as one Addr0 with
        one Segment containing two Pairs:

          - principal pair: ``sigma_chart`` (κ-side σ), structured route
            of ``child(i)`` steps over ``sigma_children``
          - aux pair: ``tau_chart`` (κ-side τ), single ``field(tau)``
            step

        The engine then runs streaming cascade:

          1. Compute ``sigma_key = (sigma_chart.id, canonical_children)``
             where ``canonical_children`` chases the path1 union-find on
             each ``sigma_children`` element.
          2. If other addr0s already share this sigma_key, they have the
             same syntactic shape but possibly different aux (τ) chart →
             emit a glue and union them in the path1 closure.
          3. After the glue, recursively re-canonicalize parent sigma_keys
             that mention any merged addr0 as a child.

        Returns the Addr0 (newly minted, or the existing canonical if
        the observation is a duplicate).
        """
        if rank is None:
            rank = self.ensure_rank()
        if patch is None:
            patch = self.ensure_patch(rank=rank)
        sort = sort or sigma_chart.root
        node_root = node_root or sigma_chart.root

        # Canonicalize children through the path1 union-find.
        canon_sigma_children = tuple(
            self._uf.find(c) for c in sigma_children
        )
        canon_tau_children = tuple(
            self._uf.find(c) for c in tau_children
        )

        sigma_key = (sigma_chart.id, canon_sigma_children)
        full_sig = (
            sort,
            sigma_chart.id,
            canon_sigma_children,
            tau_chart.id,
            canon_tau_children,
        )

        # v2 residue port: capture the raw sigma_children tuple as
        # supplied by the caller, before any canonicalization.  Used
        # by addr0_residue() to recover all the raw forms that fed
        # into a single canonical Addr0.
        raw_children_tuple = tuple(sigma_children)

        # Dedup: if an exact match already exists, return it.
        existing_addr0 = self._addr0_signature_index.get(full_sig)
        if existing_addr0 is not None:
            self._addr0_residue[existing_addr0.id].add(raw_children_tuple)
            return existing_addr0

        # Mint the new addr0.
        addr0_id = self._mint_id("addr0")
        sigma_pair = Pair(
            chart=sigma_chart.id,
            root=node_root,
            route=[
                Step(kind="child", arg=i)
                for i in range(len(sigma_children))
            ],
            role="principal",
        )
        tau_pair = Pair(
            chart=tau_chart.id,
            root=node_root,
            route=[Step(kind="field", arg="tau")],
            role="aux",
        )
        addr0 = Addr0(
            id=addr0_id,
            sort=sort,
            discoveryRank=rank.id,
            segments=[Segment(
                rank=rank.id,
                phase=patch.phase,
                patch=patch.id,
                pairs=[sigma_pair, tau_pair],
            )],
        )
        self.document.addresses0.append(addr0)
        self._uf.make(addr0_id)

        # Update registries.
        self._addr0_signature_index[full_sig] = addr0
        self._addr0_sigma_key[addr0_id] = sigma_key
        self._addr0_tau_chart[addr0_id] = tau_chart.id
        self._addr0_children[addr0_id] = canon_sigma_children
        self._addr0s_by_sigma_key[sigma_key].add(addr0_id)
        for child in canon_sigma_children:
            self._sigma_keys_by_child[child].add(sigma_key)

        # Pass 2: register the new Addr0 in all three Fibers.
        # The Fibers accumulate alongside the existing _uf and
        # _addr0_signature_index machinery; they are passive in
        # Pass 2 and do not influence emission decisions.
        self._observe_into_fibers(addr0)

        # v2 residue port: record the raw sigma_children tuple
        # against the freshly-minted Addr0 id.
        self._addr0_residue[addr0_id].add(raw_children_tuple)

        # ── Streaming glue cascade ──
        same_shape = self._addr0s_by_sigma_key[sigma_key]
        if len(same_shape) >= 2:
            self._glue_set_and_cascade(
                set(same_shape), rank, patch,
                label=f"η-glue:{sigma_chart.id}",
                collect_addr1s=[],  # streaming caller discards the list
            )

        # ── HIT collapse note ──
        # Under the HIT collapse, hash-consing happens at emission
        # time in _emit_glue, so morphism duplicates can't be
        # created during streaming ingest.  The previous
        # auto_coh_closure call here was a post-hoc canonicalization
        # pass, which is unnecessary under emission-time hash-cons.
        # auto_coh_closure remains on the engine as a backward-compat
        # wrapper around Document.canonicalize() for callers that
        # import documents from JSON or merge bundles and need
        # rank-agnostic duplicate cleanup.

        return addr0

    # ── Public glue / coh ───────────────────────────────────────

    def glue(
        self,
        src: str,
        dst: str,
        rank: Optional[Rank] = None,
        patch: Optional[Patch] = None,
        label: Optional[str] = None,
        premises: Optional[Sequence[str]] = None,
    ) -> GlueResult:
        """Add a path1 (glue) Addr1 between two Addr0s, with cascade.

        If the endpoints are already in the same path1 equivalence
        class, this is a no-op (returns a GlueResult with addr1=None,
        was_noop=True).  Otherwise it emits an Addr1 with ctor=glue,
        runs the streaming coh check (whether another glue already
        connects the same canonical pair), and runs the recursive
        cascade.

        ``premises`` is the list of Addr0 ids that justify the glue
        (it is forwarded directly to ``Addr1.premises``).  ``src``
        and ``dst`` MUST be Addr0 ids previously returned by
        ``add_observation``; the engine does not validate this.
        """
        if rank is None:
            rank = self.ensure_rank()
        if patch is None:
            patch = self.ensure_patch(rank=rank)

        if self._uf.find(src) == self._uf.find(dst):
            return GlueResult(addr1=None)

        cascade_addr1s: List[Addr1] = []
        # Seed the cascade with BOTH endpoints' pre-merge canonicals so
        # parent sigma_keys keyed under either side are found.  Looking
        # up only the post-merge canonical loses the loser's parents.
        seeds: Set[str] = {
            self._uf.find(src),
            self._uf.find(dst),
        }
        addr1 = self._emit_glue(
            src, dst, rank, patch,
            label=label or f"glue:{src}~{dst}",
            premises=list(premises or []),
        )
        self._cascade_after_merge(seeds, rank, patch, cascade_addr1s)
        return GlueResult(
            addr1=addr1,
            cascade_addr1s=cascade_addr1s,
        )

    def coh(
        self,
        src: str,
        dst: str,
        rank: Optional[Rank] = None,
        patch: Optional[Patch] = None,
        label: Optional[str] = None,
    ) -> Optional[Addr2]:
        """Add a path2 (coh) Addr2 between two Addr1s.

        Returns the new Addr2, or None if the two paths are already
        in the same path2 class.  ``src`` and ``dst`` MUST be Addr1
        ids previously returned by the engine; the engine does not
        validate this.
        """
        if self._uf.find(src) == self._uf.find(dst):
            return None
        if rank is None:
            rank = self.ensure_rank()
        if patch is None:
            patch = self.ensure_patch(rank=rank)
        addr2 = Addr2(
            id=self._mint_id("addr2"),
            rank=rank.id,
            patch=patch.id,
            ctor="coh",
            src=src,
            dst=dst,
            label=label or f"coh:{src}~{dst}",
        )
        self.document.paths2.append(addr2)
        # Pass 2: register the new Addr2 in all three Fibers.
        self._observe_into_fibers(addr2)
        self._uf.union(src, dst)
        return addr2

    # ── τ-cascade: auto-coh fixed-point pass ────────────────────

    def auto_coh_closure(self) -> List[Addr2]:
        """Run the τ-cascade fixed-point pass on the engine's Document.

        Delegates to ``self.document.auto_coh_closure()`` for the
        coh-emission logic, then also unions the resulting Addr1
        class identifiers in the engine's internal ``_addr1_uf``
        union-find so the engine's path2 state stays consistent with
        the Document's.

        Called automatically at the end of ``add_observation`` after
        the σ-cascade settles.  Also callable manually after bulk
        operations like ``merge_bundle`` or raw Document construction.
        The pass is idempotent: running it twice produces no new
        records on the second call.

        Returns the list of newly-minted Addr2 records.
        """
        new_records = self.document.auto_coh_closure()
        # Sync the engine's path2 union-find with the new cohs.
        # Most Addr1 ids were registered in _addr1_uf by _emit_glue
        # during streaming ingest, but this method is also callable
        # after manual document construction (e.g., JSON import,
        # merge_bundle, or direct append to document.paths1), so we
        # register any new ids defensively.  These .make() calls are
        # idempotent on already-known ids.
        for addr2 in new_records:
            self._uf.make(addr2.src)
            self._uf.make(addr2.dst)
            self._uf.union(addr2.src, addr2.dst)
        return new_records

    # ── Cascade internals ───────────────────────────────────────

    def _emit_glue(
        self,
        src: str,
        dst: str,
        rank: Rank,
        patch: Patch,
        label: str,
        premises: Optional[List[str]],
    ) -> Addr1:
        """Mint one Addr1 ctor=glue and union the path1 classes.

        Under the HIT collapse, this method hash-conses at
        emission time: if an Addr1 already exists with the same
        sigma_key (computed over the canonical (src, dst) pair),
        return the existing one instead of minting a duplicate.

        The hash-cons key is the **witness term** for the morphism,
        built via ``morphism_term()`` from the swap-normalized
        canonical endpoints.  The term IS the key — no separate
        encoding step.  ``morphism_term`` is the same function
        that ``sigma_key`` calls internally, so the key format
        is always in sync.

        Canonicalization happens BEFORE term construction: the
        term uses the current canonical src/dst under the
        union-find, so two _emit_glue calls with different raw
        endpoints but the same canonical pair produce the same
        term and hash-cons to one Addr1.

        The union call comes AFTER the term lookup because
        unioning changes the canonical map and would invalidate
        the key we just computed.

        Pre-HIT behavior preserved: premises, label, ctor are
        written to the minted Addr1 when it's fresh.  On hash-cons
        hit, the existing Addr1 is returned as-is; its premises
        and label are not updated with the new caller's data.
        This matches the old _emit_glue's first-writer-wins
        discipline.
        """
        # Canonicalize endpoints.
        canon_src = self._uf.find(src) if src in self._uf else src
        canon_dst = self._uf.find(dst) if dst in self._uf else dst
        # Swap-normalize so the term is invariant under swapping:
        # a glue from A to B is the same equivalence witness as
        # a glue from B to A at the path1 level.
        if canon_src > canon_dst:
            key_src, key_dst = canon_dst, canon_src
        else:
            key_src, key_dst = canon_src, canon_dst

        # The witness term IS the hash-cons key.
        key = morphism_term(
            key_src, key_dst, "glue", tuple(premises or []),
        )

        # v2 residue port: capture the raw (src, dst) pair as
        # supplied by the caller, before swap normalization and
        # canonicalization.  Used by addr1_residue() to recover
        # all the raw endpoint forms that fed into a single
        # canonical Addr1.
        raw_endpoints = (src, dst)

        # Hash-cons lookup: if a glue with this exact signature
        # already exists, return it.
        existing = self._morphism_signature_index.get(key)
        if existing is not None:
            self._addr1_residue[existing.id].add(raw_endpoints)
            return existing

        # Mint a fresh Addr1.
        addr1 = Addr1(
            id=self._mint_id("addr1"),
            rank=rank.id,
            patch=patch.id,
            ctor="glue",
            src=src,
            dst=dst,
            label=label,
            premises=list(premises or []),
        )
        self.document.paths1.append(addr1)
        self._uf.make(addr1.id)
        self._morphism_signature_index[key] = addr1
        # Pass 2: register the new Addr1 in all three Fibers.
        # See _observe_into_fibers and the Fiber section docstring.
        self._observe_into_fibers(addr1)
        # v2 residue port: record the raw (src, dst) pair against
        # the freshly-minted Addr1 id.
        self._addr1_residue[addr1.id].add(raw_endpoints)
        # Apply the union AFTER registering the sigma_key in the
        # index, because unioning changes the canonical map and
        # any future _emit_glue call computing a sigma_key would
        # see the NEW canonical.  That's fine — the new canonical
        # is consistent with the one we just stored.
        self._uf.union(src, dst)
        return addr1

    def _glue_set_and_cascade(
        self,
        addr0_ids: Set[str],
        rank: Rank,
        patch: Patch,
        label: str,
        collect_addr1s: List[Addr1],
    ) -> None:
        """Glue every addr0 in the set into a single class; recurse.

        Caller invariant: ``addr0_ids`` contains at least two ids.
        New Addr1s emitted by both this glue set and the recursive
        cascade are appended to ``collect_addr1s``.
        """
        ids = sorted(addr0_ids)
        # Capture pre-merge canonicals of every member so the cascade
        # seed sees parent sigma_keys keyed under any side.
        seeds: Set[str] = {self._uf.find(a) for a in ids}
        anchor = ids[0]
        for other in ids[1:]:
            if self._uf.find(anchor) == self._uf.find(other):
                continue
            collect_addr1s.append(self._emit_glue(
                anchor, other, rank, patch,
                label=label, premises=ids,
            ))
        self._cascade_after_merge(seeds, rank, patch, collect_addr1s)

    def _cascade_after_merge(
        self,
        merged_addr0s: Set[str],
        rank: Rank,
        patch: Patch,
        collect_addr1s: List[Addr1],
    ) -> None:
        """Re-canonicalize structural keys whose children just moved.

        For each sigma_key that mentions a merged addr0 as a child,
        rebuild the key with the new canonical child id.  If the new
        key already has occupants, glue all of them together (which
        may trigger further cascades).  Iterate to fixed point.
        """
        worklist: Set[Tuple[str, Tuple[str, ...]]] = set()
        for a in merged_addr0s:
            worklist |= self._sigma_keys_by_child.get(a, set())

        while worklist:
            keys = list(worklist)
            worklist = set()
            for old_key in keys:
                sigma_chart_id, old_children = old_key
                new_children = tuple(
                    self._uf.find(c) for c in old_children
                )
                new_key = (sigma_chart_id, new_children)
                if new_key == old_key:
                    continue

                # Move all addr0s under old_key into new_key.
                addr0s_at_old = self._addr0s_by_sigma_key.pop(old_key)
                # Detach old_key from each old child's reverse index.
                for c in old_children:
                    self._sigma_keys_by_child.get(c, set()).discard(old_key)

                if new_key in self._addr0s_by_sigma_key:
                    target = self._addr0s_by_sigma_key[new_key]
                    # Two formerly-distinct sigma classes have collided
                    # in the rekey: glue all members.
                    union_set = set(target) | set(addr0s_at_old)
                    target |= addr0s_at_old
                    for a in addr0s_at_old:
                        self._addr0_sigma_key[a] = new_key
                        self._addr0_children[a] = new_children
                    # union_set always has at least 2 elements: target
                    # has ≥1 (otherwise new_key wouldn't be in the dict)
                    # and addr0s_at_old has ≥1 (it was popped from a key
                    # that exists).  So we always glue.
                    ids = sorted(union_set)
                    # Capture pre-merge canonicals so the next-round
                    # seed sees parents keyed under any side.
                    round_seeds: Set[str] = {
                        self._uf.find(a) for a in ids
                    }
                    anchor = ids[0]
                    for other in ids[1:]:
                        if (self._uf.find(anchor)
                                == self._uf.find(other)):
                            continue
                        collect_addr1s.append(self._emit_glue(
                            anchor, other, rank, patch,
                            label=f"cascade-glue:{sigma_chart_id}",
                            premises=ids,
                        ))
                    for seed in round_seeds:
                        worklist |= self._sigma_keys_by_child.get(
                            seed, set()
                        )
                else:
                    # Fresh slot — just relabel.
                    self._addr0s_by_sigma_key[new_key] = addr0s_at_old
                    for a in addr0s_at_old:
                        self._addr0_sigma_key[a] = new_key
                        self._addr0_children[a] = new_children
                    for c in new_children:
                        self._sigma_keys_by_child[c].add(new_key)

    # ── Query interface ─────────────────────────────────────────
    #
    # Under the HIT collapse, _uf is a single union-find spanning
    # all ranks (addr0 and addr1 ids mix freely).  The query
    # methods below iterate the type-segmented Document collections
    # (``self.document.addresses0`` / ``self.document.paths1``) to
    # answer rank-specific class queries — cells know their type
    # via the dataclass that holds them, so the query API stays
    # rank-segmented without resorting to id-string inspection.

    def canonical_addr0(self, addr0_id: str) -> str:
        """Return the canonical Addr0 id under the path1 union-find."""
        return self._uf.find(addr0_id)

    def canonical_addr1(self, addr1_id: str) -> str:
        """Return the canonical Addr1 id under the path2 union-find."""
        return self._uf.find(addr1_id)

    def addr0_class(self, addr0_id: str) -> Set[str]:
        """All addr0 ids in the same path1 equivalence class."""
        canon = self.canonical_addr0(addr0_id)
        return {
            a.id for a in self.document.addresses0
            if a.id in self._uf and self._uf.find(a.id) == canon
        }

    def addr1_class(self, addr1_id: str) -> Set[str]:
        """All addr1 ids in the same path2 equivalence class."""
        canon = self.canonical_addr1(addr1_id)
        return {
            a.id for a in self.document.paths1
            if a.id in self._uf and self._uf.find(a.id) == canon
        }

    def all_addr0_classes(self) -> Dict[str, Set[str]]:
        """Map every canonical addr0 id to its full path1 class."""
        out: Dict[str, Set[str]] = defaultdict(set)
        for a in self.document.addresses0:
            if a.id in self._uf:
                out[self._uf.find(a.id)].add(a.id)
        return dict(out)

    def all_addr1_classes(self) -> Dict[str, Set[str]]:
        """Map every canonical addr1 id to its full path2 class."""
        out: Dict[str, Set[str]] = defaultdict(set)
        for a in self.document.paths1:
            if a.id in self._uf:
                out[self._uf.find(a.id)].add(a.id)
        return dict(out)

    # ── Reading-(a) projection: κ as Pair.role ──────────────────

    def role_coproduct_view(
        self,
    ) -> Dict[str, Dict[str, List[Tuple[str, Pair]]]]:
        """Reading-(a) projection of the κ = σ ⊎_τ σ coproduct.

        For each chart in the document, returns a partition of all
        its incoming Pairs by role:

            { chart_id: { 'principal': [(addr0_id, pair), ...],
                          'aux':       [(addr0_id, pair), ...] } }

        This is the *derived* view in which κ surfaces as the
        principal/aux discriminator on every Pair, dual to the
        implementation-primary reading (b) where κ surfaces as
        ``Chart.kind``.

        Pedagogically: under reading (b) we ask "what's this chart's
        kind?" and get sigma or tau.  Under reading (a) we ask "what
        roles do the pairs play under this chart?" and get the same
        information re-projected as the canonical/auxiliary structure
        of observations within each chart.  Both readings agree on
        every Document because the engine emits the principal pair on
        the σ chart and the aux pair on the τ chart by construction.
        """
        out: Dict[str, Dict[str, List[Tuple[str, Pair]]]] = {}
        for chart in self.document.charts:
            out[chart.id] = {"principal": [], "aux": []}
        for addr0 in self.document.addresses0:
            for segment in addr0.segments:
                for pair in segment.pairs:
                    bucket = out.setdefault(
                        pair.chart, {"principal": [], "aux": []}
                    )
                    bucket.setdefault(pair.role, []).append((addr0.id, pair))
        return out

    # ── Document health ─────────────────────────────────────────

    def receipt(self):  # type: ignore[no-untyped-def]
        """Pass-through to ``self.document.receipt()`` for convenience."""
        return self.document.receipt()

    def __repr__(self) -> str:
        return (
            "PFFCascadeEngine("
            f"doc={self.document.documentId!r}, "
            f"addr0={len(self.document.addresses0)}, "
            f"path1={len(self.document.paths1)}, "
            f"path2={len(self.document.paths2)}, "
            f"charts={len(self.document.charts)})"
        )


__all__ = [
    "PFFCascadeEngine",
    "GlueResult",
]
