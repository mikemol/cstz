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
    Chart,
    Document,
    Pair,
    Patch,
    Rank,
    Segment,
    Step,
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

        # path1 / path2 union-finds
        self._addr0_uf: _UnionFind = _UnionFind()
        self._addr1_uf: _UnionFind = _UnionFind()

        # ── Registries (signatures → records) ──
        # Records are stored directly so lookups never need a second
        # pass through the document.  Correct-by-construction: every
        # entry in a registry is also in the document by virtue of
        # both being appended together.
        self._chart_registry: Dict[Tuple[str, str, Any], Chart] = {}
        self._rank_by_ordinal: Dict[int, Rank] = {}
        self._patch_by_phase: Dict[Tuple[str, str], Patch] = {}
        self._addr0_signature_index: Dict[Tuple[Any, ...], Addr0] = {}

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

    # ── Id minting ──────────────────────────────────────────────

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
            self._addr0_uf.find(c) for c in sigma_children
        )
        canon_tau_children = tuple(
            self._addr0_uf.find(c) for c in tau_children
        )

        sigma_key = (sigma_chart.id, canon_sigma_children)
        full_sig = (
            sort,
            sigma_chart.id,
            canon_sigma_children,
            tau_chart.id,
            canon_tau_children,
        )

        # Dedup: if an exact match already exists, return it.
        existing_addr0 = self._addr0_signature_index.get(full_sig)
        if existing_addr0 is not None:
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
        self._addr0_uf.make(addr0_id)

        # Update registries.
        self._addr0_signature_index[full_sig] = addr0
        self._addr0_sigma_key[addr0_id] = sigma_key
        self._addr0_tau_chart[addr0_id] = tau_chart.id
        self._addr0_children[addr0_id] = canon_sigma_children
        self._addr0s_by_sigma_key[sigma_key].add(addr0_id)
        for child in canon_sigma_children:
            self._sigma_keys_by_child[child].add(sigma_key)

        # ── Streaming glue cascade ──
        same_shape = self._addr0s_by_sigma_key[sigma_key]
        if len(same_shape) >= 2:
            self._glue_set_and_cascade(
                set(same_shape), rank, patch,
                label=f"η-glue:{sigma_chart.id}",
                collect_addr1s=[],  # streaming caller discards the list
            )

        # ── Streaming τ-cascade (auto-coh) ──
        # After the σ-cascade settles its path1 state, run the dual
        # τ-cascade at path2: group Addr1 records by canonical endpoint
        # pair and emit cohs to unify witnesses.  See auto_coh_closure
        # docstring and rhpf-pff-profiles/AUDIT.md §"The τ-Slicer and
        # the asymmetry it exposes" for design rationale.
        self.auto_coh_closure()

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

        if self._addr0_uf.find(src) == self._addr0_uf.find(dst):
            return GlueResult(addr1=None)

        cascade_addr1s: List[Addr1] = []
        # Seed the cascade with BOTH endpoints' pre-merge canonicals so
        # parent sigma_keys keyed under either side are found.  Looking
        # up only the post-merge canonical loses the loser's parents.
        seeds: Set[str] = {
            self._addr0_uf.find(src),
            self._addr0_uf.find(dst),
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
        if self._addr1_uf.find(src) == self._addr1_uf.find(dst):
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
        self._addr1_uf.union(src, dst)
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
            self._addr1_uf.make(addr2.src)
            self._addr1_uf.make(addr2.dst)
            self._addr1_uf.union(addr2.src, addr2.dst)
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
        """Mint one Addr1 ctor=glue and union the path1 classes."""
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
        self._addr1_uf.make(addr1.id)
        self._addr0_uf.union(src, dst)
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
        seeds: Set[str] = {self._addr0_uf.find(a) for a in ids}
        anchor = ids[0]
        for other in ids[1:]:
            if self._addr0_uf.find(anchor) == self._addr0_uf.find(other):
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
                    self._addr0_uf.find(c) for c in old_children
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
                        self._addr0_uf.find(a) for a in ids
                    }
                    anchor = ids[0]
                    for other in ids[1:]:
                        if (self._addr0_uf.find(anchor)
                                == self._addr0_uf.find(other)):
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

    def canonical_addr0(self, addr0_id: str) -> str:
        """Return the canonical Addr0 id under the path1 union-find."""
        return self._addr0_uf.find(addr0_id)

    def canonical_addr1(self, addr1_id: str) -> str:
        """Return the canonical Addr1 id under the path2 union-find."""
        return self._addr1_uf.find(addr1_id)

    def addr0_class(self, addr0_id: str) -> Set[str]:
        """All addr0 ids in the same path1 equivalence class."""
        canon = self.canonical_addr0(addr0_id)
        return {a for a in self._addr0_uf if self._addr0_uf.find(a) == canon}

    def addr1_class(self, addr1_id: str) -> Set[str]:
        """All addr1 ids in the same path2 equivalence class."""
        canon = self.canonical_addr1(addr1_id)
        return {a for a in self._addr1_uf if self._addr1_uf.find(a) == canon}

    def all_addr0_classes(self) -> Dict[str, Set[str]]:
        """Map every canonical addr0 id to its full path1 class."""
        out: Dict[str, Set[str]] = defaultdict(set)
        for a in self._addr0_uf:
            out[self._addr0_uf.find(a)].add(a)
        return dict(out)

    def all_addr1_classes(self) -> Dict[str, Set[str]]:
        """Map every canonical addr1 id to its full path2 class."""
        out: Dict[str, Set[str]] = defaultdict(set)
        for a in self._addr1_uf:
            out[self._addr1_uf.find(a)].add(a)
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
