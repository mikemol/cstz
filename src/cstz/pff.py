"""PFF / RHPF data model — Layer 1 of cstz.

This module is a faithful Python implementation of the Path Forest Format
(PFF/1.0) information model defined in `rhpf-pff-profiles/`.  It is the
authoritative storage layer that the rest of cstz is being realigned onto.

Vocabulary correspondence (cstz today ↔ PFF):

    core.SPPF                                ↔  Document
    core.Fiber                               ↔  Chart system + addr0 collection
    core.FiberClass.signature                ↔  Pair (chart, route)
    core.FiberClass.fid                      ↔  Addr0.id
    _eta_tower entries                       ↔  Addr1 with ctor: glue
    abstraction-merge collisions             ↔  Addr2 with ctor: coh
    _cleavage_levels[i]                      ↔  Boundary with Ports
    Cascade rounds                           ↔  Rank.ordinal values
    Pair.role principal/aux                  ↔  κ = σ ⊎_τ σ coproduct discriminator

The normative information model is **flat and document-scoped**: patches,
charts, addresses, paths, class views, and shadows all live at document
scope.  Patches do not own anything by nesting; they only refer to other
records by document-local identifier.

This module provides:

  - Pure dataclasses for every PFF construct
  - Validators implementing the SHACL well-formedness rules
  - JSON serialization conforming to `pff.schema.json`
  - A `Document.merge_bundle` operation that alpha-renames on collision
    and emits a `DocumentReceipt` with structured `ValidationIssue`s

The cascade engine — union-find / glue closure / coh — is layered on top
of these dataclasses by `core.SPPF` (Step 2 of the realignment).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    Iterator,
    List,
    Mapping,
    Optional,
    Tuple,
    Union,
)


# ── Identifier discipline ───────────────────────────────────────────
#
# All identifiers in a PFF document are document-local.  Two documents
# may safely use overlapping identifier strings; on merge the incoming
# bundle is alpha-renamed against the host document's namespace.

PFF_VERSION = "1.0"
IDENTIFIER_SCOPE = "document-local"

# Enumerations from the schema, lifted to module-level constants so
# tests and adapters can reference them without re-typing the strings.
STEP_KINDS: Tuple[str, ...] = ("child", "field", "pack", "share", "port")
HOP_SIDES: Tuple[str, ...] = ("left", "right", "both")
PAIR_ROLES: Tuple[str, ...] = ("principal", "aux")
ADDR1_CTORS: Tuple[str, ...] = (
    "refl", "glue", "transport", "pack", "compose", "inverse", "named",
)
ADDR2_CTORS: Tuple[str, ...] = (
    "coh", "vcomp", "hcomp", "whisker", "named2",
)
SHADOW_NODE_KINDS: Tuple[str, ...] = ("semantic", "packed", "intermediate")
SHADOW_EDGE_KINDS: Tuple[str, ...] = ("contains", "premise", "projectsTo")
WF_STATUSES: Tuple[str, ...] = ("clean", "stored-with-violations", "rejected")
SEVERITIES: Tuple[str, ...] = ("info", "warning", "error", "fatal")


# ── Atomic records ──────────────────────────────────────────────────


@dataclass
class Rank:
    """A document-local rank: an ordinal-tagged identifier.

    Ranks are strictly ordered by `ordinal`.  Within a single Addr0,
    segment ranks must be strictly increasing (WF-1).
    """

    id: str
    ordinal: int
    label: Optional[str] = None
    note: Optional[str] = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {"id": self.id, "ordinal": self.ordinal}
        if self.label is not None:
            out["label"] = self.label
        if self.note is not None:
            out["note"] = self.note
        return out


@dataclass
class Port:
    """A named slot on a Boundary."""

    name: str
    role: Optional[str] = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {"name": self.name}
        if self.role is not None:
            out["role"] = self.role
        return out


@dataclass
class Boundary:
    """A boundary collects ports.  Patches attach via leftBoundary/rightBoundary."""

    id: str
    ports: List[Port] = field(default_factory=list)

    def to_json(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "ports": [p.to_json() for p in self.ports],
        }

    def has_port(self, name: str) -> bool:
        return any(p.name == name for p in self.ports)


@dataclass
class Patch:
    """A document-scoped patch: phase + rank + optional boundaries.

    Patches are *not* ownership containers.  They only carry metadata.
    Charts, addresses, and paths live at document scope and reference
    a patch by id when relevant.
    """

    id: str
    rank: str  # references a Rank.id
    phase: str
    leftBoundary: Optional[str] = None
    rightBoundary: Optional[str] = None
    label: Optional[str] = None
    meta: Optional[Dict[str, Any]] = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "id": self.id,
            "rank": self.rank,
            "phase": self.phase,
        }
        if self.leftBoundary is not None:
            out["leftBoundary"] = self.leftBoundary
        if self.rightBoundary is not None:
            out["rightBoundary"] = self.rightBoundary
        if self.label is not None:
            out["label"] = self.label
        if self.meta is not None:
            out["meta"] = dict(self.meta)
        return out


@dataclass
class Chart:
    """A chart: an identified perspective rooted at a node string.

    In cstz this is the σ-fiber or τ-fiber view depending on payload.
    The discriminator κ = σ ⊎_τ σ surfaces at the *Pair* level via
    `Pair.role`, not at the chart level.
    """

    id: str
    root: str
    patch: Optional[str] = None
    kind: Optional[str] = None
    payload: Any = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {"id": self.id, "root": self.root}
        if self.patch is not None:
            out["patch"] = self.patch
        if self.kind is not None:
            out["kind"] = self.kind
        if self.payload is not None:
            out["payload"] = self.payload
        return out


@dataclass
class Step:
    """A canonical route step.  The structured form is normative."""

    kind: str  # one of STEP_KINDS
    arg: Optional[Union[str, int]] = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {"kind": self.kind}
        if self.arg is not None:
            out["arg"] = self.arg
        return out


@dataclass
class Hop:
    """A boundary crossing within a pair."""

    boundary: str
    side: str  # one of HOP_SIDES
    port: str

    def to_json(self) -> Dict[str, Any]:
        return {"boundary": self.boundary, "side": self.side, "port": self.port}


@dataclass
class Pair:
    """A (chart, root, route, role) cell.

    Each pair is a directed observation rooted at `root` in `chart`,
    reached by traversing the structured `route`.  `role` is the
    κ = σ ⊎_τ σ coproduct discriminator: principal pairs project the
    σ-side, aux pairs project the τ-side.
    """

    chart: str
    root: str
    route: List[Step] = field(default_factory=list)
    boundary: List[Hop] = field(default_factory=list)
    role: str = "principal"  # one of PAIR_ROLES

    def to_json(self) -> Dict[str, Any]:
        return {
            "chart": self.chart,
            "root": self.root,
            "route": [s.to_json() for s in self.route],
            "boundary": [h.to_json() for h in self.boundary],
            "role": self.role,
        }


@dataclass
class Segment:
    """A rank-tagged collection of pairs within an Addr0."""

    rank: str  # references a Rank.id
    phase: str
    patch: str  # references a Patch.id
    pairs: List[Pair] = field(default_factory=list)

    def to_json(self) -> Dict[str, Any]:
        return {
            "rank": self.rank,
            "phase": self.phase,
            "patch": self.patch,
            "pairs": [p.to_json() for p in self.pairs],
        }


@dataclass
class Addr0:
    """An order-0 address: identity for a node observed across ranks.

    Segment ranks within an Addr0 are strictly increasing (WF-1).
    """

    id: str
    segments: List[Segment]
    sort: Optional[str] = None
    discoveryRank: Optional[str] = None
    payload: Any = None
    meta: Optional[Dict[str, Any]] = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "id": self.id,
            "segments": [s.to_json() for s in self.segments],
        }
        if self.sort is not None:
            out["sort"] = self.sort
        if self.discoveryRank is not None:
            out["discoveryRank"] = self.discoveryRank
        if self.payload is not None:
            out["payload"] = self.payload
        if self.meta is not None:
            out["meta"] = dict(self.meta)
        return out


@dataclass
class Addr1:
    """An order-1 path: a glue/transport between two Addr0s.

    `ctor: glue` corresponds to cstz's η-merges; `ctor: refl` to identity;
    `ctor: compose` to chained glue.
    """

    id: str
    rank: str
    ctor: str  # one of ADDR1_CTORS
    src: str
    dst: str
    patch: Optional[str] = None
    boundary: Optional[str] = None
    premises: List[str] = field(default_factory=list)
    label: Optional[str] = None
    args: Optional[Dict[str, Any]] = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "id": self.id,
            "rank": self.rank,
            "ctor": self.ctor,
            "src": self.src,
            "dst": self.dst,
            "premises": list(self.premises),
        }
        if self.patch is not None:
            out["patch"] = self.patch
        if self.boundary is not None:
            out["boundary"] = self.boundary
        if self.label is not None:
            out["label"] = self.label
        if self.args is not None:
            out["args"] = dict(self.args)
        return out


@dataclass
class Addr2:
    """An order-2 path: a coherence between two Addr1s.

    `ctor: coh` corresponds to cstz's abstraction-merge confluences.
    """

    id: str
    rank: str
    ctor: str  # one of ADDR2_CTORS
    src: str
    dst: str
    patch: Optional[str] = None
    label: Optional[str] = None
    args: Optional[Dict[str, Any]] = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "id": self.id,
            "rank": self.rank,
            "ctor": self.ctor,
            "src": self.src,
            "dst": self.dst,
        }
        if self.patch is not None:
            out["patch"] = self.patch
        if self.label is not None:
            out["label"] = self.label
        if self.args is not None:
            out["args"] = dict(self.args)
        return out


# ── Derived views (non-authoritative) ───────────────────────────────


@dataclass
class ClassMember:
    """A membership record linking an Addr0 into a ClassView."""

    classId: str
    address0: str

    def to_json(self) -> Dict[str, Any]:
        return {"classId": self.classId, "address0": self.address0}


@dataclass
class ClassView:
    """A derived equivalence-class view.  Never authoritative."""

    id: str
    rank: str
    phase: str
    truncation: str
    congruence: str
    members: List[ClassMember] = field(default_factory=list)
    policy: Optional[str] = None
    isAuthoritative: bool = False  # SHACL: must be False

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "id": self.id,
            "rank": self.rank,
            "phase": self.phase,
            "truncation": self.truncation,
            "congruence": self.congruence,
            "members": [m.to_json() for m in self.members],
            "isAuthoritative": False,
        }
        if self.policy is not None:
            out["policy"] = self.policy
        return out


@dataclass
class ShadowNode:
    id: str
    kind: str  # one of SHADOW_NODE_KINDS
    label: Optional[str] = None
    backing: List[str] = field(default_factory=list)

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "id": self.id,
            "kind": self.kind,
            "backing": list(self.backing),
        }
        if self.label is not None:
            out["label"] = self.label
        return out


@dataclass
class ShadowEdge:
    src: str
    dst: str
    kind: str  # one of SHADOW_EDGE_KINDS
    ordinal: Optional[int] = None

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {"src": self.src, "dst": self.dst, "kind": self.kind}
        if self.ordinal is not None:
            out["ordinal"] = self.ordinal
        return out


@dataclass
class Shadow:
    """A derived SPPF-like shadow at a (rank, phase, truncation) point."""

    id: str
    rank: str
    phase: str
    truncation: str
    congruence: str
    nodes: List[ShadowNode] = field(default_factory=list)
    edges: List[ShadowEdge] = field(default_factory=list)
    policy: Optional[str] = None
    isAuthoritative: bool = False  # SHACL: must be False

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "id": self.id,
            "rank": self.rank,
            "phase": self.phase,
            "truncation": self.truncation,
            "congruence": self.congruence,
            "nodes": [n.to_json() for n in self.nodes],
            "edges": [e.to_json() for e in self.edges],
            "isAuthoritative": False,
        }
        if self.policy is not None:
            out["policy"] = self.policy
        return out


# ── Validation: ValidationIssue + DocumentReceipt ───────────────────


@dataclass
class ValidationIssue:
    """A structured well-formedness issue.

    Matches the OpenAPI schema: rule, location, severity, message.
    Severity ∈ {info, warning, error, fatal}.  Fatal issues prevent
    storage; non-fatal issues yield a 207 (stored-with-violations).
    """

    rule: str
    location: str
    severity: str
    message: str

    def __post_init__(self) -> None:
        if self.severity not in SEVERITIES:
            raise ValueError(
                f"unknown severity {self.severity!r}; expected one of {SEVERITIES}"
            )

    def to_json(self) -> Dict[str, Any]:
        return {
            "rule": self.rule,
            "location": self.location,
            "severity": self.severity,
            "message": self.message,
        }


@dataclass
class DocumentReceipt:
    """A merge / store receipt.  Matches the OpenAPI DocumentReceipt schema."""

    documentId: str
    accepted: bool
    wfStatus: str  # one of WF_STATUSES
    violations: List[ValidationIssue] = field(default_factory=list)
    rank: Optional[str] = None
    warnings: List[str] = field(default_factory=list)

    def to_json(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "documentId": self.documentId,
            "accepted": self.accepted,
            "wfStatus": self.wfStatus,
            "violations": [v.to_json() for v in self.violations],
        }
        if self.rank is not None:
            out["rank"] = self.rank
        if self.warnings:
            out["warnings"] = list(self.warnings)
        return out

    @property
    def http_status(self) -> int:
        """Return the recommended HTTP status per pff.core.md §6."""
        if not self.accepted:
            return 422
        if any(v.severity in ("error", "fatal") for v in self.violations):
            # Defensive: errors imply rejection in our discipline,
            # but if anyone constructs an accepted receipt with errors,
            # treat it as 207.
            return 207  # pragma: no cover
        if self.violations:
            return 207
        return 200


# ── PatchBundle ─────────────────────────────────────────────────────


@dataclass
class PatchBundle:
    """A flat document-scoped contribution to a Document.

    PatchBundles do not own charts or addresses; they contribute them
    to the host document on merge.  Identifier collisions are resolved
    by alpha-rename of the incoming side.
    """

    patches: List[Patch] = field(default_factory=list)
    boundaries: List[Boundary] = field(default_factory=list)
    charts: List[Chart] = field(default_factory=list)
    addresses0: List[Addr0] = field(default_factory=list)
    paths1: List[Addr1] = field(default_factory=list)
    paths2: List[Addr2] = field(default_factory=list)
    ranks: List[Rank] = field(default_factory=list)

    def to_json(self) -> Dict[str, Any]:
        return {
            "version": PFF_VERSION,
            "identifierScope": IDENTIFIER_SCOPE,
            "patches": [p.to_json() for p in self.patches],
            "boundaries": [b.to_json() for b in self.boundaries],
            "charts": [c.to_json() for c in self.charts],
            "addresses0": [a.to_json() for a in self.addresses0],
            "paths1": [p.to_json() for p in self.paths1],
            "paths2": [p.to_json() for p in self.paths2],
            "ranks": [r.to_json() for r in self.ranks],
        }


# ── Linear-algebraic helpers ────────────────────────────────────────
#
# These two functions implement the F₂ kernel computation that
# Document.path1_classes / path2_classes (and their canonical-map
# variants) sit on top of.  They are module-level so the methods
# can stay short and read declaratively.


def _kernel_projection(
    elements: Iterable[str],
    edges: Iterable[Tuple[str, str]],
) -> Dict[str, str]:
    """Compute the kernel projection of an F₂ boundary map.

    Given a finite set of vertex ids and a list of edges, returns a
    map from each vertex to the lex-smallest member of its connected
    component.  This is the kernel of the boundary map ∂ : F₂^E →
    F₂^V projected onto representatives, computed by union-find with
    path compression.

    Lex-smallest is chosen as the canonical representative for
    deterministic, choice-independent output across runs.
    """
    parent: Dict[str, str] = {e: e for e in elements}

    def find(x: str) -> str:
        r = x
        while parent[r] != r:
            r = parent[r]
        while parent[x] != r:
            parent[x], x = r, parent[x]
        return r

    def union(a: str, b: str) -> None:
        ra, rb = find(a), find(b)
        if ra == rb:
            return
        if ra < rb:
            parent[rb] = ra
        else:
            parent[ra] = rb

    for a, b in edges:
        union(a, b)

    return {x: find(x) for x in parent}


def _classes_from_canonical_map(
    canonical: Dict[str, str],
) -> List[FrozenSet[str]]:
    """Group a canonical map into a sorted list of equivalence classes."""
    classes: Dict[str, set] = {}
    for member, canon in canonical.items():
        classes.setdefault(canon, set()).add(member)
    return sorted(
        (frozenset(s) for s in classes.values()),
        key=lambda s: min(s),
    )


# ── Document ────────────────────────────────────────────────────────


@dataclass
class Document:
    """A PFF document: the authoritative store.

    Layer 1 of cstz.  Pure data + validators + alpha-rename merge.
    The cascade engine (union-find / glue / coh) is layered on top of
    this by `core.SPPF` in Step 2 of the realignment.
    """

    documentId: str
    ranks: List[Rank] = field(default_factory=list)
    patches: List[Patch] = field(default_factory=list)
    boundaries: List[Boundary] = field(default_factory=list)
    charts: List[Chart] = field(default_factory=list)
    addresses0: List[Addr0] = field(default_factory=list)
    paths1: List[Addr1] = field(default_factory=list)
    paths2: List[Addr2] = field(default_factory=list)
    classViews: List[ClassView] = field(default_factory=list)
    shadows: List[Shadow] = field(default_factory=list)
    baseIri: Optional[str] = None
    namespaces: Optional[Dict[str, str]] = None

    # ── Iteration / lookup helpers ──────────────────────────────────

    def rank_by_id(self, rank_id: str) -> Optional[Rank]:
        for r in self.ranks:
            if r.id == rank_id:
                return r
        return None

    def patch_by_id(self, patch_id: str) -> Optional[Patch]:
        for p in self.patches:
            if p.id == patch_id:
                return p
        return None

    def chart_by_id(self, chart_id: str) -> Optional[Chart]:
        for c in self.charts:
            if c.id == chart_id:
                return c
        return None

    def boundary_by_id(self, boundary_id: str) -> Optional[Boundary]:
        for b in self.boundaries:
            if b.id == boundary_id:
                return b
        return None

    def addr0_by_id(self, addr0_id: str) -> Optional[Addr0]:
        for a in self.addresses0:
            if a.id == addr0_id:
                return a
        return None

    # ── All identifiers (for alpha-rename) ──────────────────────────

    def all_identifiers(self) -> Iterator[str]:
        for r in self.ranks:
            yield r.id
        for p in self.patches:
            yield p.id
        for b in self.boundaries:
            yield b.id
        for c in self.charts:
            yield c.id
        for a in self.addresses0:
            yield a.id
        for p1 in self.paths1:
            yield p1.id
        for p2 in self.paths2:
            yield p2.id
        for cv in self.classViews:
            yield cv.id
        for sh in self.shadows:
            yield sh.id

    # ── Validation (SHACL constraints) ──────────────────────────────

    def validate(self) -> List[ValidationIssue]:
        """Run every well-formedness check; return all violations.

        Validators correspond directly to the SHACL shapes in
        pff.shacl.ttl.  This is intentionally a Python re-encoding of
        those rules so we don't pull a SHACL engine into the runtime.
        """
        issues: List[ValidationIssue] = []
        issues.extend(self._validate_required_collections())
        issues.extend(self._validate_unique_ids())
        issues.extend(self._validate_rank_references())
        issues.extend(self._validate_patch_references())
        issues.extend(self._validate_chart_references())
        issues.extend(self._validate_addr0_segments())
        issues.extend(self._validate_pairs())
        issues.extend(self._validate_path_endpoints())
        issues.extend(self._validate_derived_views())
        return issues

    def _validate_required_collections(self) -> List[ValidationIssue]:
        issues: List[ValidationIssue] = []
        if not self.ranks:
            issues.append(ValidationIssue(
                rule="DocumentShape",
                location="/ranks",
                severity="fatal",
                message="document must declare at least one rank",
            ))
        return issues

    def _validate_unique_ids(self) -> List[ValidationIssue]:
        """Each collection must have unique ids within its kind."""
        issues: List[ValidationIssue] = []
        for kind, items in (
            ("ranks", self.ranks),
            ("patches", self.patches),
            ("boundaries", self.boundaries),
            ("charts", self.charts),
            ("addresses0", self.addresses0),
            ("paths1", self.paths1),
            ("paths2", self.paths2),
            ("classViews", self.classViews),
            ("shadows", self.shadows),
        ):
            seen: Dict[str, int] = {}
            for idx, item in enumerate(items):
                ident = getattr(item, "id")
                if ident in seen:
                    issues.append(ValidationIssue(
                        rule="UniqueId",
                        location=f"/{kind}/{idx}",
                        severity="fatal",
                        message=f"duplicate id {ident!r} in {kind}",
                    ))
                else:
                    seen[ident] = idx
        return issues

    def _validate_rank_references(self) -> List[ValidationIssue]:
        issues: List[ValidationIssue] = []
        rank_ids = {r.id for r in self.ranks}
        for idx, p in enumerate(self.patches):
            if p.rank not in rank_ids:
                issues.append(ValidationIssue(
                    rule="PatchShape.patchRank",
                    location=f"/patches/{idx}/rank",
                    severity="fatal",
                    message=f"patch {p.id!r} references unknown rank {p.rank!r}",
                ))
        for idx, p in enumerate(self.paths1):
            if p.rank not in rank_ids:
                issues.append(ValidationIssue(
                    rule="Addr1Shape.rank",
                    location=f"/paths1/{idx}/rank",
                    severity="fatal",
                    message=f"path1 {p.id!r} references unknown rank {p.rank!r}",
                ))
        for idx, p in enumerate(self.paths2):
            if p.rank not in rank_ids:
                issues.append(ValidationIssue(
                    rule="Addr2Shape.rank",
                    location=f"/paths2/{idx}/rank",
                    severity="fatal",
                    message=f"path2 {p.id!r} references unknown rank {p.rank!r}",
                ))
        return issues

    def _validate_patch_references(self) -> List[ValidationIssue]:
        issues: List[ValidationIssue] = []
        patch_ids = {p.id for p in self.patches}
        boundary_ids = {b.id for b in self.boundaries}
        for idx, p in enumerate(self.patches):
            if p.leftBoundary is not None and p.leftBoundary not in boundary_ids:
                issues.append(ValidationIssue(
                    rule="PatchShape.leftBoundary",
                    location=f"/patches/{idx}/leftBoundary",
                    severity="error",
                    message=f"patch {p.id!r} references unknown boundary {p.leftBoundary!r}",
                ))
            if p.rightBoundary is not None and p.rightBoundary not in boundary_ids:
                issues.append(ValidationIssue(
                    rule="PatchShape.rightBoundary",
                    location=f"/patches/{idx}/rightBoundary",
                    severity="error",
                    message=f"patch {p.id!r} references unknown boundary {p.rightBoundary!r}",
                ))
        for idx, c in enumerate(self.charts):
            if c.patch is not None and c.patch not in patch_ids:
                issues.append(ValidationIssue(
                    rule="ChartShape.patch",
                    location=f"/charts/{idx}/patch",
                    severity="error",
                    message=f"chart {c.id!r} references unknown patch {c.patch!r}",
                ))
        return issues

    def _validate_chart_references(self) -> List[ValidationIssue]:
        issues: List[ValidationIssue] = []
        for idx, c in enumerate(self.charts):
            if not c.root:
                issues.append(ValidationIssue(
                    rule="ChartShape.chartRoot",
                    location=f"/charts/{idx}/root",
                    severity="fatal",
                    message=f"chart {c.id!r} has empty root",
                ))
        return issues

    def _validate_addr0_segments(self) -> List[ValidationIssue]:
        """WF-1: segment ranks within an Addr0 are strictly increasing."""
        issues: List[ValidationIssue] = []
        rank_ord: Dict[str, int] = {r.id: r.ordinal for r in self.ranks}
        for ai, addr in enumerate(self.addresses0):
            if not addr.segments:
                issues.append(ValidationIssue(
                    rule="Addr0Shape.hasSegment",
                    location=f"/addresses0/{ai}/segments",
                    severity="fatal",
                    message=f"addr0 {addr.id!r} has no segments",
                ))
                continue
            seen_ranks: Dict[str, int] = {}
            prev_ordinal: Optional[int] = None
            for si, seg in enumerate(addr.segments):
                if seg.rank in seen_ranks:
                    issues.append(ValidationIssue(
                        rule="UniqueSegmentRankPerAddr0",
                        location=f"/addresses0/{ai}/segments/{si}/rank",
                        severity="fatal",
                        message=(
                            f"addr0 {addr.id!r} contains two segments at "
                            f"rank {seg.rank!r}"
                        ),
                    ))
                seen_ranks[seg.rank] = si
                ord_value = rank_ord.get(seg.rank)
                if ord_value is None:
                    issues.append(ValidationIssue(
                        rule="SegmentShape.segmentRank",
                        location=f"/addresses0/{ai}/segments/{si}/rank",
                        severity="fatal",
                        message=(
                            f"segment in addr0 {addr.id!r} references unknown "
                            f"rank {seg.rank!r}"
                        ),
                    ))
                    continue
                if prev_ordinal is not None and ord_value <= prev_ordinal:
                    issues.append(ValidationIssue(
                        rule="MonotoneSegmentChain",
                        location=f"/addresses0/{ai}/segments/{si}/rank",
                        severity="fatal",
                        message=(
                            f"segment ranks in addr0 {addr.id!r} are not "
                            f"strictly increasing at index {si}"
                        ),
                    ))
                prev_ordinal = ord_value
        return issues

    def _validate_pairs(self) -> List[ValidationIssue]:
        """Per-pair checks: chart ref, role enum, hop port compatibility."""
        issues: List[ValidationIssue] = []
        chart_ids = {c.id for c in self.charts}
        patch_ids = {p.id for p in self.patches}
        boundaries: Dict[str, Boundary] = {b.id: b for b in self.boundaries}
        for ai, addr in enumerate(self.addresses0):
            for si, seg in enumerate(addr.segments):
                if seg.patch not in patch_ids:
                    issues.append(ValidationIssue(
                        rule="SegmentShape.segmentPatch",
                        location=f"/addresses0/{ai}/segments/{si}/patch",
                        severity="fatal",
                        message=(
                            f"segment in addr0 {addr.id!r} references unknown "
                            f"patch {seg.patch!r}"
                        ),
                    ))
                if not seg.pairs:
                    issues.append(ValidationIssue(
                        rule="SegmentShape.hasPair",
                        location=f"/addresses0/{ai}/segments/{si}/pairs",
                        severity="fatal",
                        message=(
                            f"segment in addr0 {addr.id!r} at rank {seg.rank!r} "
                            f"has no pairs"
                        ),
                    ))
                for pi, pair in enumerate(seg.pairs):
                    base = f"/addresses0/{ai}/segments/{si}/pairs/{pi}"
                    if pair.chart not in chart_ids:
                        issues.append(ValidationIssue(
                            rule="PairShape.pairChart",
                            location=f"{base}/chart",
                            severity="fatal",
                            message=f"pair references unknown chart {pair.chart!r}",
                        ))
                    if pair.role not in PAIR_ROLES:
                        issues.append(ValidationIssue(
                            rule="PairShape.pairRole",
                            location=f"{base}/role",
                            severity="fatal",
                            message=(
                                f"pair role {pair.role!r} not in {PAIR_ROLES}"
                            ),
                        ))
                    seen_steps: Dict[int, int] = {}
                    for ki, step in enumerate(pair.route):
                        if step.kind not in STEP_KINDS:
                            issues.append(ValidationIssue(
                                rule="StepShape.stepKind",
                                location=f"{base}/route/{ki}/kind",
                                severity="fatal",
                                message=(
                                    f"step kind {step.kind!r} not in {STEP_KINDS}"
                                ),
                            ))
                        if ki in seen_steps:  # pragma: no cover
                            # Index reuse via list iteration is impossible
                            # because ki is the loop counter; kept for the
                            # SHACL UniqueStepIndex shape parity.
                            issues.append(ValidationIssue(
                                rule="UniqueStepIndex",
                                location=f"{base}/route/{ki}",
                                severity="error",
                                message="duplicate step index in pair route",
                            ))
                        seen_steps[ki] = ki
                    for hi, hop in enumerate(pair.boundary):
                        if hop.side not in HOP_SIDES:
                            issues.append(ValidationIssue(
                                rule="HopShape.hopSide",
                                location=f"{base}/boundary/{hi}/side",
                                severity="fatal",
                                message=f"hop side {hop.side!r} not in {HOP_SIDES}",
                            ))
                        b = boundaries.get(hop.boundary)
                        if b is None:
                            issues.append(ValidationIssue(
                                rule="HopShape.hopBoundary",
                                location=f"{base}/boundary/{hi}/boundary",
                                severity="error",
                                message=(
                                    f"hop references unknown boundary "
                                    f"{hop.boundary!r}"
                                ),
                            ))
                        elif not b.has_port(hop.port):
                            issues.append(ValidationIssue(
                                rule="BoundaryPortCompatibility",
                                location=f"{base}/boundary/{hi}/port",
                                severity="error",
                                message=(
                                    f"hop port {hop.port!r} not on boundary "
                                    f"{hop.boundary!r}"
                                ),
                            ))
        return issues

    def _validate_path_endpoints(self) -> List[ValidationIssue]:
        issues: List[ValidationIssue] = []
        addr0_ids = {a.id for a in self.addresses0}
        path1_ids = {p.id for p in self.paths1}
        for idx, p in enumerate(self.paths1):
            if p.ctor not in ADDR1_CTORS:
                issues.append(ValidationIssue(
                    rule="Addr1Shape.ctor",
                    location=f"/paths1/{idx}/ctor",
                    severity="fatal",
                    message=f"path1 {p.id!r} has ctor {p.ctor!r} not in {ADDR1_CTORS}",
                ))
            if p.src not in addr0_ids:
                issues.append(ValidationIssue(
                    rule="Addr1Shape.src",
                    location=f"/paths1/{idx}/src",
                    severity="error",
                    message=f"path1 {p.id!r} src {p.src!r} not an addr0",
                ))
            if p.dst not in addr0_ids:
                issues.append(ValidationIssue(
                    rule="Addr1Shape.dst",
                    location=f"/paths1/{idx}/dst",
                    severity="error",
                    message=f"path1 {p.id!r} dst {p.dst!r} not an addr0",
                ))
        for idx, p in enumerate(self.paths2):
            if p.ctor not in ADDR2_CTORS:
                issues.append(ValidationIssue(
                    rule="Addr2Shape.ctor",
                    location=f"/paths2/{idx}/ctor",
                    severity="fatal",
                    message=f"path2 {p.id!r} has ctor {p.ctor!r} not in {ADDR2_CTORS}",
                ))
            if p.src not in path1_ids:
                issues.append(ValidationIssue(
                    rule="Addr2Shape.src",
                    location=f"/paths2/{idx}/src",
                    severity="error",
                    message=f"path2 {p.id!r} src {p.src!r} not a path1",
                ))
            if p.dst not in path1_ids:
                issues.append(ValidationIssue(
                    rule="Addr2Shape.dst",
                    location=f"/paths2/{idx}/dst",
                    severity="error",
                    message=f"path2 {p.id!r} dst {p.dst!r} not a path1",
                ))
        return issues

    def _validate_derived_views(self) -> List[ValidationIssue]:
        issues: List[ValidationIssue] = []
        for idx, cv in enumerate(self.classViews):
            if cv.isAuthoritative:
                issues.append(ValidationIssue(
                    rule="ClassViewShape.isAuthoritative",
                    location=f"/classViews/{idx}/isAuthoritative",
                    severity="fatal",
                    message="ClassView must declare isAuthoritative=false",
                ))
        for idx, sh in enumerate(self.shadows):
            if sh.isAuthoritative:
                issues.append(ValidationIssue(
                    rule="ShadowShape.isAuthoritative",
                    location=f"/shadows/{idx}/isAuthoritative",
                    severity="fatal",
                    message="Shadow must declare isAuthoritative=false",
                ))
        return issues

    # ── Linear-algebraic view (F₂ boundary maps) ────────────────────
    #
    # A pff.Document encodes its path1 / path2 closures in two
    # equivalent ways:
    #
    #   - Operationally, as the sequence of Addr1(glue) / Addr2(coh)
    #     records in `self.paths1` / `self.paths2`.
    #
    #   - Mathematically, as the kernel of an F₂ boundary map.  For
    #     a graph G with V = Addr0 ids and E = Addr1(glue) edges,
    #     the path1 partition is the basis of H₀(G; F₂) = F₂^V /
    #     im(∂), where ∂ : F₂^E → F₂^V sends each glue (a, b) to the
    #     formal sum e_a + e_b.  Computing connected components =
    #     computing the cokernel of ∂ = solving Ax = 0 over F₂.
    #
    # The methods below surface the second view directly.  They
    # compute the partition from a Document's `paths1` / `paths2`
    # collection alone, with no dependence on PFFCascadeEngine, and
    # are guaranteed by construction to agree with the cascade's
    # `_addr0_uf` / `_addr1_uf` partitions when the document was
    # produced by an engine.  This is verified by tests in
    # tests/test_pff_cascade.py::TestLinearViewCrossCheck.

    def path1_constraint_rows(self) -> List[Tuple[str, str]]:
        """The rows of the F₂ boundary map ∂_1 : F₂^{glues} → F₂^{addr0s}.

        Each row is the formal sum e_src + e_dst for an Addr1 with
        ``ctor ∈ {glue, refl}``.  Other ctors (transport, compose,
        inverse, pack, named) are not part of the path1 closure and
        are skipped.
        """
        return [
            (p1.src, p1.dst)
            for p1 in self.paths1
            if p1.ctor in ("glue", "refl")
        ]

    def path1_canonical_map(self) -> Dict[str, str]:
        """Return ``addr0_id → canonical_addr0_id`` for the path1 closure.

        The canonical representative of each equivalence class is the
        lex-smallest member, chosen for deterministic output.  This
        is the kernel projection of the F₂ boundary map ∂_1.
        """
        return _kernel_projection(
            (a.id for a in self.addresses0),
            self.path1_constraint_rows(),
        )

    def path1_classes(self) -> List[FrozenSet[str]]:
        """Return the path1 partition as a list of equivalence classes.

        Equivalent to ``H_0(G_glue; F_2)`` where G_glue has Addr0
        vertices and Addr1(glue) edges.  The list is sorted by the
        lex-smallest id in each class for deterministic output.
        """
        return _classes_from_canonical_map(self.path1_canonical_map())

    def path2_constraint_rows(self) -> List[Tuple[str, str]]:
        """The rows of the F₂ boundary map ∂_2 : F₂^{cohs} → F₂^{path1s}.

        Each row is the formal sum e_src + e_dst for an Addr2 with
        ``ctor = coh``.  Other ctors (vcomp, hcomp, whisker, named2)
        are not part of the path2 closure and are skipped.
        """
        return [
            (p2.src, p2.dst)
            for p2 in self.paths2
            if p2.ctor == "coh"
        ]

    def path2_canonical_map(self) -> Dict[str, str]:
        """Return ``addr1_id → canonical_addr1_id`` for the path2 closure."""
        return _kernel_projection(
            (p1.id for p1 in self.paths1),
            self.path2_constraint_rows(),
        )

    def path2_classes(self) -> List[FrozenSet[str]]:
        """Return the path2 partition as a list of equivalence classes."""
        return _classes_from_canonical_map(self.path2_canonical_map())

    # ── Grothendieck topology view (Slicer output) ──────────────────
    #
    # The σ-Slicer and τ-Slicer of the topos-theoretic framing both
    # produce Grothendieck topologies at the cascade fixed point.
    # The σ-Slicer's topology is the path1 partition over Addr0 ids;
    # the τ-Slicer's topology is the path2 partition over Addr1 ids.
    # Both are fully computable from a Document alone, because at
    # the cascade fixed point the sigma-key equivalence class
    # partition equals the path1 partition (and analogously for τ).
    # See rhpf-pff-profiles/AUDIT.md's Slicer postscript for the
    # theorem + proof.
    #
    # These accessors are semantic aliases for path1_classes() /
    # path2_classes() with docstrings that reframe the partition
    # as Grothendieck-topology covering sieves.  No new computation.

    def covering_sieves_over_addr0(self) -> List[FrozenSet[str]]:
        """σ-Slicer output: the Grothendieck topology over Addr0 ids.

        Each frozen set is a covering sieve — a maximal set of Addr0s
        that were identified as structurally equivalent at the cascade
        fixed point.  The three Grothendieck-topology axioms are
        maintained by the cascade as invariants:

          - Identity cover: every Addr0 is in a sieve containing itself
          - Stability under pullback: adding more observations never
            removes an existing sieve's members (monotonicity)
          - Transitivity: the sieves are closed under the transitive
            closure of structural-key equivalence

        The return value is the same partition as ``path1_classes()``
        (by the σ-key ≡ path1 theorem at the cascade fixed point).
        """
        return self.path1_classes()

    def covering_sieve_for_addr0(self, addr0_id: str) -> FrozenSet[str]:
        """Return the σ-covering sieve containing a given Addr0."""
        canonical = self.path1_canonical_map()[addr0_id]
        return frozenset(
            a for a, c in self.path1_canonical_map().items() if c == canonical
        )

    def covering_sieves_over_addr1(self) -> List[FrozenSet[str]]:
        """τ-Slicer output: the Grothendieck topology over Addr1 ids.

        Each frozen set is a covering sieve at the path2 level — a
        maximal set of Addr1 glue records that were identified as
        coherent at the cascade fixed point (via user-declared cohs,
        and as of a future commit, via auto-coh fixed-point closure).

        Mirrors ``covering_sieves_over_addr0`` at the path2 level.
        The return value is the same partition as ``path2_classes()``.
        """
        return self.path2_classes()

    def covering_sieve_for_addr1(self, addr1_id: str) -> FrozenSet[str]:
        """Return the τ-covering sieve containing a given Addr1."""
        canonical = self.path2_canonical_map()[addr1_id]
        return frozenset(
            a for a, c in self.path2_canonical_map().items() if c == canonical
        )

    # ── τ-cascade: auto-coh fixed-point pass ────────────────────────
    #
    # The σ-cascade (in pff_cascade.PFFCascadeEngine) auto-emits Addr1s
    # whenever two observations share a sigma-key during streaming
    # ingest.  The τ-cascade is the dual operation one rank up: it
    # scans the paths1 collection and auto-emits Addr2 (ctor=coh)
    # records between any two Addr1 records witnessing the same
    # canonical endpoint pair under the current path1 partition.
    #
    # The pass is one-shot (no recursive re-canonicalization needed)
    # because emitting cohs only unions the path2 union-find and does
    # not affect the path1 canonical map, so the grouping keys are
    # stable during the scan.  This is the key asymmetry with the
    # σ-cascade: σ-key collisions can cascade because child
    # canonicalization can change under a merge, whereas τ-cascade
    # cohs don't affect the endpoint canonicals they're grouping on.
    #
    # The pass is idempotent: running it twice produces no new records
    # on the second call.
    #
    # Under normal σ-cascade operation the pass emits zero cohs (the
    # σ-cascade's skip-check in _glue_set_and_cascade prevents
    # duplicates).  It fires on:
    #
    #   - Documents produced by Document.merge_bundle() where both
    #     sides independently glued the same canonical pair
    #   - User-constructed Documents with manually-added duplicate
    #     Addr1 records
    #   - Any future refactor that removes the σ-cascade's
    #     emission-dedup logic
    #
    # See rhpf-pff-profiles/AUDIT.md §"The τ-Slicer and the
    # asymmetry it exposes" for the design rationale.

    def auto_coh_closure(self) -> List[Addr2]:
        """Run the τ-cascade fixed-point pass on this document.

        Scans ``self.paths1`` and groups Addr1 records by their
        canonical endpoint pair (under the current path1 partition),
        normalized so `(a, b)` and `(b, a)` are the same group.
        For each group with ≥2 members, emits one Addr2 with
        ``ctor="coh"`` per pair of members that are not yet in the
        same path2 class, using lex-smallest-first anchor ordering.

        Returns the list of newly-minted Addr2 records.  Empty on a
        document that's already at its τ-cascade fixed point.

        The newly-minted Addr2 records are appended to
        ``self.paths2``.  Their ids follow the pattern
        ``auto-coh-N`` where N counts from the current length of
        ``paths2``, guaranteeing uniqueness within the Document.

        Ranks and patches for the new records:
            - rank: the lex-smallest rank id found on any of the
              grouped Addr1 records (conservative choice that
              keeps the coh at the same rank level as its witnesses)
            - patch: the first path2 record's patch if any exist,
              else the first path1 record's patch, else None
        """
        path1_canon = self.path1_canonical_map()

        # Step 1: partition path1_ids by the normalized canonical
        # endpoint pair.  Order within each group is list-position
        # (ingest order) for deterministic output.
        #
        # The canonical pair is computed under the current path1
        # partition.  If two Addr1 records already sit in the same
        # path1 class (meaning the cascade already knows their
        # endpoints are equivalent at the Addr0 level), they are
        # candidates for being cohered even if their declared raw
        # endpoints differ — that's the whole point of running this
        # pass after the σ-cascade has converged.
        groups: Dict[Tuple[str, str], List[str]] = {}
        # Preserve a side index from group key → representative raw
        # endpoint pair for labeling purposes, chosen from the
        # first Addr1 to enter each group.
        raw_pair_of: Dict[Tuple[str, str], Tuple[str, str]] = {}
        for p1 in self.paths1:
            if p1.ctor not in ("glue", "refl"):
                # Non-merge ctors (transport, compose, inverse,
                # pack, named) don't assert path1 equivalence, so
                # they don't participate in τ-coherence.
                continue
            # For glue/refl Addr1s, the path1 closure unions src and
            # dst into the same class, so src_canon == dst_canon.
            # The normalized group key is the doubled canonical.
            src_canon = path1_canon[p1.src]
            dst_canon = path1_canon[p1.dst]
            key = (src_canon, dst_canon)
            groups.setdefault(key, []).append(p1.id)
            # Record the first Addr1's raw (pre-canonicalization)
            # endpoints for the label, normalized lex-smallest-first.
            if key not in raw_pair_of:
                raw_src, raw_dst = sorted((p1.src, p1.dst))
                raw_pair_of[key] = (raw_src, raw_dst)

        # Step 2: compute the current path2 canonical map; we use it
        # to skip cohs that would be redundant with existing ones.
        path2_canon = self.path2_canonical_map()

        # Step 3: for each group with ≥2 members, emit cohs in an
        # anchor-first pattern (lex-smallest id as anchor; all other
        # members get a coh to the anchor).  This is the same
        # emit-merges-in-group pattern as the σ-cascade's
        # _glue_set_and_cascade inner loop, but for path2 instead
        # of path1.
        #
        # Note: this method is written as a self-contained loop
        # rather than delegating to a shared _emit_merges_in_group
        # helper.  That's intentional — the parallel implementation
        # strategy keeps the σ-cascade untouched until the auto-coh
        # pass has its own tests validating it.  A follow-up commit
        # will extract the shared inner-loop helper.
        new_records: List[Addr2] = []
        next_ordinal = len(self.paths2)

        # Default rank / patch to use when the chosen Addr1 records
        # don't agree.  Use the lex-smallest rank id that appears on
        # any member.
        def _conservative_rank(member_ids: List[str]) -> Optional[str]:
            ranks_seen = {
                p.rank for p in self.paths1 if p.id in set(member_ids)
            }
            return min(ranks_seen) if ranks_seen else None

        def _conservative_patch(member_ids: List[str]) -> Optional[str]:
            for p in self.paths1:
                if p.id in set(member_ids) and p.patch is not None:
                    return p.patch
            return None

        for (src, dst), members in groups.items():
            if len(members) < 2:
                continue
            # Sort members by id for deterministic anchor selection
            sorted_members = sorted(members)
            anchor = sorted_members[0]
            for other in sorted_members[1:]:
                anchor_canon = path2_canon.get(anchor, anchor)
                other_canon = path2_canon.get(other, other)
                if anchor_canon == other_canon:
                    # Already in the same path2 class; skip
                    continue
                rank = _conservative_rank([anchor, other])
                patch = _conservative_patch([anchor, other])
                raw_src, raw_dst = raw_pair_of[(src, dst)]
                new_addr2 = Addr2(
                    id=f"auto-coh-{next_ordinal}",
                    rank=rank if rank is not None else "",
                    ctor="coh",
                    src=anchor,
                    dst=other,
                    patch=patch,
                    label=f"auto-coh:{raw_src}~{raw_dst}",
                )
                self.paths2.append(new_addr2)
                new_records.append(new_addr2)
                next_ordinal += 1
                # Update path2_canon on the fly so subsequent
                # iterations see the newly-emitted union.  The
                # anchor-first pattern means `anchor` stays as
                # the winner throughout the group, and each
                # `other_canon → anchor_canon` update is a single
                # hop — no chained rename propagation is needed.
                winner = min(anchor_canon, other_canon)
                loser = max(anchor_canon, other_canon)
                path2_canon[loser] = winner

        return new_records

    # ── Receipts ────────────────────────────────────────────────────

    def receipt(self) -> DocumentReceipt:
        """Validate the document and emit a structured receipt."""
        violations = self.validate()
        fatal = any(v.severity == "fatal" for v in violations)
        if fatal:
            wf = "rejected"
            accepted = False
        elif violations:
            wf = "stored-with-violations"
            accepted = True
        else:
            wf = "clean"
            accepted = True
        return DocumentReceipt(
            documentId=self.documentId,
            accepted=accepted,
            wfStatus=wf,
            violations=violations,
        )

    # ── JSON ────────────────────────────────────────────────────────

    def to_pff_json(self) -> Dict[str, Any]:
        """Serialize the document into pff.schema.json conforming JSON."""
        out: Dict[str, Any] = {
            "version": PFF_VERSION,
            "documentId": self.documentId,
            "identifierScope": IDENTIFIER_SCOPE,
            "ranks": [r.to_json() for r in self.ranks],
            "patches": [p.to_json() for p in self.patches],
            "boundaries": [b.to_json() for b in self.boundaries],
            "charts": [c.to_json() for c in self.charts],
            "addresses0": [a.to_json() for a in self.addresses0],
            "paths1": [p.to_json() for p in self.paths1],
            "paths2": [p.to_json() for p in self.paths2],
            "classViews": [cv.to_json() for cv in self.classViews],
            "shadows": [sh.to_json() for sh in self.shadows],
        }
        if self.baseIri is not None:
            out["baseIri"] = self.baseIri
        if self.namespaces:
            out["namespaces"] = dict(self.namespaces)
        return out

    # ── Merge ───────────────────────────────────────────────────────

    def merge_bundle(self, bundle: PatchBundle) -> DocumentReceipt:
        """Merge a PatchBundle into this document, alpha-renaming on collision.

        Identifier collisions are resolved by renaming the *incoming* side
        with a suffix.  After alpha-rename, every cross-reference within
        the bundle is rewritten to use the new identifiers, then the
        records are appended to the document and the document is
        re-validated.
        """
        rename = self._build_rename_map(bundle)

        # Apply renames and append.  Each accessor below copies through
        # `rename` so the bundle's internal references stay coherent.
        for r in bundle.ranks:
            self.ranks.append(Rank(
                id=rename.get(r.id, r.id),
                ordinal=r.ordinal,
                label=r.label,
                note=r.note,
            ))
        for b in bundle.boundaries:
            self.boundaries.append(Boundary(
                id=rename.get(b.id, b.id),
                ports=[Port(name=p.name, role=p.role) for p in b.ports],
            ))
        for p in bundle.patches:
            self.patches.append(Patch(
                id=rename.get(p.id, p.id),
                rank=rename.get(p.rank, p.rank),
                phase=p.phase,
                leftBoundary=(
                    rename.get(p.leftBoundary, p.leftBoundary)
                    if p.leftBoundary is not None else None
                ),
                rightBoundary=(
                    rename.get(p.rightBoundary, p.rightBoundary)
                    if p.rightBoundary is not None else None
                ),
                label=p.label,
                meta=dict(p.meta) if p.meta is not None else None,
            ))
        for c in bundle.charts:
            self.charts.append(Chart(
                id=rename.get(c.id, c.id),
                root=c.root,
                patch=rename.get(c.patch, c.patch) if c.patch is not None else None,
                kind=c.kind,
                payload=c.payload,
            ))
        for a in bundle.addresses0:
            self.addresses0.append(Addr0(
                id=rename.get(a.id, a.id),
                segments=[
                    Segment(
                        rank=rename.get(s.rank, s.rank),
                        phase=s.phase,
                        patch=rename.get(s.patch, s.patch),
                        pairs=[
                            Pair(
                                chart=rename.get(pr.chart, pr.chart),
                                root=pr.root,
                                route=[Step(kind=st.kind, arg=st.arg) for st in pr.route],
                                boundary=[
                                    Hop(
                                        boundary=rename.get(h.boundary, h.boundary),
                                        side=h.side,
                                        port=h.port,
                                    )
                                    for h in pr.boundary
                                ],
                                role=pr.role,
                            )
                            for pr in s.pairs
                        ],
                    )
                    for s in a.segments
                ],
                sort=a.sort,
                discoveryRank=(
                    rename.get(a.discoveryRank, a.discoveryRank)
                    if a.discoveryRank is not None else None
                ),
                payload=a.payload,
                meta=dict(a.meta) if a.meta is not None else None,
            ))
        for p1 in bundle.paths1:
            self.paths1.append(Addr1(
                id=rename.get(p1.id, p1.id),
                rank=rename.get(p1.rank, p1.rank),
                ctor=p1.ctor,
                src=rename.get(p1.src, p1.src),
                dst=rename.get(p1.dst, p1.dst),
                patch=rename.get(p1.patch, p1.patch) if p1.patch is not None else None,
                boundary=(
                    rename.get(p1.boundary, p1.boundary)
                    if p1.boundary is not None else None
                ),
                premises=[rename.get(pr, pr) for pr in p1.premises],
                label=p1.label,
                args=dict(p1.args) if p1.args is not None else None,
            ))
        for p2 in bundle.paths2:
            self.paths2.append(Addr2(
                id=rename.get(p2.id, p2.id),
                rank=rename.get(p2.rank, p2.rank),
                ctor=p2.ctor,
                src=rename.get(p2.src, p2.src),
                dst=rename.get(p2.dst, p2.dst),
                patch=rename.get(p2.patch, p2.patch) if p2.patch is not None else None,
                label=p2.label,
                args=dict(p2.args) if p2.args is not None else None,
            ))

        return self.receipt()

    def _build_rename_map(self, bundle: PatchBundle) -> Dict[str, str]:
        """Compute alpha-rename map for an incoming bundle.

        Each colliding incoming id is suffixed with `~N` where N is the
        smallest positive integer that yields a fresh id in the union of
        the document's existing ids and previously chosen rename targets.
        """
        existing = set(self.all_identifiers())
        rename: Dict[str, str] = {}
        for ident in self._iter_bundle_ids(bundle):
            if ident in existing:
                n = 1
                candidate = f"{ident}~{n}"
                while candidate in existing:
                    n += 1
                    candidate = f"{ident}~{n}"
                rename[ident] = candidate
                existing.add(candidate)
            else:
                existing.add(ident)
        return rename

    @staticmethod
    def _iter_bundle_ids(bundle: PatchBundle) -> Iterator[str]:
        for r in bundle.ranks:
            yield r.id
        for p in bundle.patches:
            yield p.id
        for b in bundle.boundaries:
            yield b.id
        for c in bundle.charts:
            yield c.id
        for a in bundle.addresses0:
            yield a.id
        for p1 in bundle.paths1:
            yield p1.id
        for p2 in bundle.paths2:
            yield p2.id


__all__ = [
    "PFF_VERSION",
    "IDENTIFIER_SCOPE",
    "STEP_KINDS",
    "HOP_SIDES",
    "PAIR_ROLES",
    "ADDR1_CTORS",
    "ADDR2_CTORS",
    "SHADOW_NODE_KINDS",
    "SHADOW_EDGE_KINDS",
    "WF_STATUSES",
    "SEVERITIES",
    "Rank",
    "Port",
    "Boundary",
    "Patch",
    "Chart",
    "Step",
    "Hop",
    "Pair",
    "Segment",
    "Addr0",
    "Addr1",
    "Addr2",
    "ClassMember",
    "ClassView",
    "ShadowNode",
    "ShadowEdge",
    "Shadow",
    "ValidationIssue",
    "DocumentReceipt",
    "PatchBundle",
    "Document",
]
