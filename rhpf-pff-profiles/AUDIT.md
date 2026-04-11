# PFF Implementation Audit (cstz)

**Audited revision:** `015ee43` (2026-04-10)
**Auditor:** read-only conformance audit, no code changes
**Subject:** the parallel PFF stack in `cstz.pff` / `cstz.pff_cascade` /
`cstz.pff_python_classifier` plus the additive
`cstz.agda_synth.synthesize_from_document` extension.  The legacy SPPF
stack (`core.py`, `python_classifier.py`, `byte_classifier.py`,
`agda_synth.synthesize`) is **not** audited here — it is the
metamathematical reference and predates the PFF vocabulary.

## Status legend

- ✅ **CONFORMS** — implemented, tested, no divergence from spec
- 🟡 **PARTIAL** — implemented but incomplete or undertested
- ❌ **MISSING** — not implemented at all
- ⚠️ **DIVERGENT** — implemented but the encoding diverges from the
  spec text (usually a structural simplification with equivalent or
  stronger guarantees)
- ⏸️ **DEFERRED** — intentionally out of scope per the realignment
  plan; conformance notes describe what would close the gap

## Summary

| Spec file | ✅ | 🟡 | ❌ | ⚠️ | ⏸️ |
|---|---|---|---|---|---|
| `pff.core.md` (6 §§) | 6 | 0 | 0 | 0 | 0 |
| `pff.schema.json` (19 $defs) | 17 | 0 | 0 | 2 | 0 |
| `pff.shacl.ttl` (15 shapes) | 11 | 0 | 0 | 2 | 2 |
| `pff.openapi.yaml` (4 endpoints) | 0 | 0 | 0 | 0 | 4 |
| `pff.sql` (19 tables + 2 views) | 0 | 0 | 0 | 0 | 21 |
| `pff.rdf.ttl` (19 classes + ontology) | 0 | 0 | 0 | 0 | 1 |
| `pff.context.jsonld` (24 classes + 50+ terms) | 0 | 0 | 0 | 0 | 1 |
| `pff.amr.md` (Penman projection) | 0 | 0 | 0 | 0 | 1 |
| **TOTAL** | **34** | **0** | **0** | **4** | **30** |

The implemented surface (specs 1–3) is **34 ✅ + 4 ⚠️** with no
missing or partial items.  All four ⚠️ entries are intentional
encoding choices that take stronger-than-spec guarantees by
construction.  The deferred surface (specs 4–8) is 30 items, all
documented with conformance notes.

---

## 1. `pff.core.md` — Core profile (6 normative sections)

### §1. Flat document-scoped information model — ✅ CONFORMS

The spec says: "`patches`, `boundaries`, `charts`, `addresses0`,
`paths1`, `paths2`, `classViews`, and `shadows` all live at document
scope.  A patch does not own an address, chart, or path by nesting.
It only links to them by identifier."

**Implementation:** [src/cstz/pff.py:579](../src/cstz/pff.py#L579)
`Document` dataclass — every collection is a top-level field
(`ranks`, `patches`, `boundaries`, `charts`, `addresses0`, `paths1`,
`paths2`, `classViews`, `shadows`).  `Patch` carries no owned
collections; it has only `id`, `rank`, `phase`, `leftBoundary`,
`rightBoundary`, `label`, `meta`.

**Tests:** [tests/test_pff.py::test_to_pff_json_minimal](../tests/test_pff.py),
[::test_lookup_helpers](../tests/test_pff.py),
[::test_all_identifiers_yields_every_id_kind](../tests/test_pff.py).

### §2. Identifier scope = document-local — ✅ CONFORMS

The spec says: "All local identifiers in a PFF document are
**document-local**, including rank IDs… When merging two documents,
an implementation MUST alpha-rename incoming local identifiers on
collision unless the merge policy explicitly declares that the
identifiers are already aligned."

**Implementation:** [src/cstz/pff.py:60](../src/cstz/pff.py#L60)
`IDENTIFIER_SCOPE = "document-local"` constant; emitted in every
`Document.to_pff_json()` and `PatchBundle.to_json()`.
Alpha-rename in [src/cstz/pff.py:1054](../src/cstz/pff.py#L1054)
`Document.merge_bundle` → [pff.py:1169](../src/cstz/pff.py#L1169)
`_build_rename_map`.  Colliding incoming ids are renamed `<id>~N`
where N is the smallest free integer.  All cross-references inside
the bundle (`rank`, `patch`, `src`, `dst`, `boundary`, `premises`,
chart `patch`, segment `rank`/`patch`, etc.) are rewritten via the
same rename map before append.

**Tests:** [tests/test_pff.py::test_merge_no_collision_appends_records](../tests/test_pff.py),
[::test_merge_renames_colliding_ids_and_rewrites_references](../tests/test_pff.py),
[::test_merge_repeated_collisions_pick_distinct_suffixes](../tests/test_pff.py),
[::test_merge_full_bundle_preserves_internal_references](../tests/test_pff.py),
[::test_merge_into_empty_doc](../tests/test_pff.py).

### §3. Segment monotonicity (WF-1) — ✅ CONFORMS

The spec says: "Within one `Addr0`, segment ranks are **strictly
increasing** by rank ordinal.  A single `Addr0` MUST NOT contain two
segments for the same rank."

**Implementation:** [src/cstz/pff.py:785](../src/cstz/pff.py#L785)
`Document._validate_addr0_segments` — for each Addr0, walks segments
in list order, tracks `prev_ordinal` and `seen_ranks`, and emits one
violation per offense:
- `Addr0Shape.hasSegment` (severity=fatal) for empty segment lists
- `UniqueSegmentRankPerAddr0` (fatal) for duplicate rank ids
- `SegmentShape.segmentRank` (fatal) for unknown rank ids
- `MonotoneSegmentChain` (fatal) for non-strictly-increasing ordinals

**Tests:** [tests/test_pff.py::test_addr0_without_segments_is_fatal](../tests/test_pff.py),
[::test_addr0_duplicate_segment_rank_is_fatal](../tests/test_pff.py),
[::test_addr0_segment_unknown_rank_is_fatal](../tests/test_pff.py),
[::test_addr0_non_monotone_segments](../tests/test_pff.py).

### §4. Canonical structured route form — ✅ CONFORMS

The spec says: "The canonical route form is the structured step
sequence… A dotted route string such as `child(2).field(lhs)` is a
conforming text serialization profile."

**Implementation:** [src/cstz/pff.py:195](../src/cstz/pff.py#L195)
`Step` is a dataclass with `kind: str` and `arg: Optional[Union[str,
int]]`.  `Pair.route: List[Step]` is the canonical form.  No dotted
text serialization is implemented (the spec marks it as a presentation
profile, not normative storage).

**Tests:** [tests/test_pff.py::test_step_to_json](../tests/test_pff.py),
[::test_pair_to_json](../tests/test_pff.py),
[::test_pair_invalid_step_kind](../tests/test_pff.py).

### §5. Derived views are non-authoritative — ✅ CONFORMS

The spec says: "`ClassView` and `Shadow` are derived views.  They
are never authoritative.  Any conforming serialization of those
views MUST declare: `truncation`, `congruence`, `isAuthoritative =
false`."

**Implementation:** [src/cstz/pff.py:381](../src/cstz/pff.py#L381)
`ClassView` and [pff.py:441](../src/cstz/pff.py#L441) `Shadow`
both have `isAuthoritative: bool = False`.  Their `to_json()`
methods hardcode `"isAuthoritative": False` in the output.  Both
require `congruence` and `truncation` as non-optional fields (no
default), so a Document cannot construct one without them.
[pff.py:986](../src/cstz/pff.py#L986)
`_validate_derived_views` emits `ClassViewShape.isAuthoritative` /
`ShadowShape.isAuthoritative` (severity=fatal) if any caller manages
to set `isAuthoritative=True`.

**Tests:** [tests/test_pff.py::test_classview_full_and_minimal](../tests/test_pff.py),
[::test_shadow_full_and_minimal](../tests/test_pff.py),
[::test_classview_must_be_non_authoritative](../tests/test_pff.py),
[::test_shadow_must_be_non_authoritative](../tests/test_pff.py),
[::test_non_authoritative_views_pass_validation](../tests/test_pff.py).

### §6. API discipline — ✅ CONFORMS (data model only)

The spec says: "Merge/write APIs should return structured validation
issues with at least: `rule`, `location`, `severity`, `message`.
Recommended merge status discipline: 200 clean / 207 stored-with-
violations / 422 rejected."

**Implementation:** [src/cstz/pff.py:474](../src/cstz/pff.py#L474)
`ValidationIssue` is a dataclass with exactly those four fields plus
`__post_init__` enforcement that severity ∈ `{info, warning, error,
fatal}`.  [pff.py:503](../src/cstz/pff.py#L503) `DocumentReceipt`
has `documentId`, `accepted`, `wfStatus`, `violations`, `rank`,
`warnings`.  Its `http_status` property implements the 200/207/422
mapping per spec text.  `Document.receipt()` builds the receipt
from `validate()`'s output, marking fatal violations as `rejected`
(422), non-fatal as `stored-with-violations` (207), clean as
`clean` (200).

The HTTP transport surface itself (the four OpenAPI endpoints) is
deferred — see §`pff.openapi.yaml` below.  The DATA discipline (the
shape and meaning of receipts and issues) is fully conformant.

**Tests:** [tests/test_pff.py::test_validation_issue_to_json](../tests/test_pff.py),
[::test_validation_issue_rejects_unknown_severity](../tests/test_pff.py),
[::test_receipt_clean_is_200](../tests/test_pff.py),
[::test_receipt_warnings_is_207](../tests/test_pff.py),
[::test_receipt_rejected_is_422](../tests/test_pff.py),
[::test_receipt_stored_with_violations_for_non_fatal_issues](../tests/test_pff.py),
[::test_minimal_doc_is_clean](../tests/test_pff.py),
[::test_empty_doc_is_rejected](../tests/test_pff.py).

---

## 2. `pff.schema.json` — JSON Schema (19 $defs)

Status: 17 ✅ + 2 ⚠️ = 19 defs covered.

For each `$defs` entry, "implementation" cites the corresponding
dataclass in [src/cstz/pff.py](../src/cstz/pff.py).  The
`to_json()` method on each dataclass produces output that conforms
to the schema's `required` field list and `unevaluatedProperties:
false` discipline.  Schema spot-check (run during the audit)
emits a populated Document via the cascade engine and confirms the
JSON shape matches every required field on every $def used.

| $def | Status | Dataclass | Notes |
|---|---|---|---|
| `Identifier` | ✅ | (string type) | All ids are strings; pattern not enforced at runtime but the engine never mints non-conforming ids |
| `QNameOrIri` | ✅ | (string type) | `phase` fields are free strings, conformant by construction |
| `Rank` | ✅ | `Rank` (pff.py:82) | required: id, ordinal — both required dataclass fields |
| `Patch` | ✅ | `Patch` (pff.py:135) | required: id, rank, phase — all required dataclass fields |
| `Boundary` | ✅ | `Boundary` (pff.py:118) | required: id; ports default `[]` |
| `Port` | ✅ | `Port` (pff.py:104) | required: name |
| `Chart` | ✅ | `Chart` (pff.py:169) | required: id, root |
| `Addr0` | ✅ | `Addr0` (pff.py:265) | required: id, segments; segments has `minItems: 1` and `_validate_addr0_segments` enforces this |
| `Segment` | ✅ | `Segment` (pff.py:247) | required: rank, phase, patch, pairs; pairs has `minItems: 1` enforced by `_validate_pairs` |
| `Pair` | ✅ | `Pair` (pff.py:221) | required: chart, root, route, role |
| `Step` | ⚠️ | `Step` (pff.py:195) | **DIVERGENT — see note below** |
| `Hop` | ✅ | `Hop` (pff.py:209) | required: boundary, side, port |
| `Addr1` | ✅ | `Addr1` (pff.py:295) | required: id, rank, ctor, src, dst; ctor enum enforced |
| `Addr2` | ✅ | `Addr2` (pff.py:334) | required: id, rank, ctor, src, dst; ctor enum enforced |
| `ClassView` | ✅ | `ClassView` (pff.py:381) | required: id, rank, phase, truncation, congruence, members, isAuthoritative; isAuthoritative const-false enforced |
| `ClassMember` | ✅ | `ClassMember` (pff.py:370) | required: classId, address0 |
| `Shadow` | ✅ | `Shadow` (pff.py:441) | required: id, rank, phase, truncation, congruence, isAuthoritative, nodes |
| `ShadowNode` | ✅ | `ShadowNode` (pff.py:409) | required: id, kind |
| `ShadowEdge` | ⚠️ | `ShadowEdge` (pff.py:427) | **DIVERGENT — see note below** |

### Schema $defs/Step — ⚠️ DIVERGENT

The schema's `$defs/Step` defines a step as `{kind, arg?}` (no
explicit ordering field).  The SHACL `StepShape`, however, says
`stepIndex` is required (`sh:minCount 1; sh:datatype xsd:integer`).
The schema and SHACL are themselves inconsistent on whether steps
have an explicit numeric index.

**Our encoding:** Steps are positionally ordered by their position
in `Pair.route: List[Step]`.  No `stepIndex` field exists on the
`Step` dataclass, and `to_json()` does not emit one.  This is
**equivalent to or stronger than** the SHACL constraint, because:

1. Positional ordering cannot have duplicates by construction.
2. The schema (which is the JSON-Schema-conformance contract) does
   not require `stepIndex`, so our output validates against it.
3. The SHACL `UniqueStepIndex` constraint becomes vacuously true
   (no two list positions can be the same integer).

The audit marks this ⚠️ rather than ✅ because the SHACL spec text
literally says `stepIndex` is required, and our encoding cannot be
losslessly round-tripped through a SHACL validator that expects an
explicit `pff:stepIndex` predicate.

**Closing the gap (if desired):** add an `index: int` field to
`Step` and emit it on `to_json()`; populate it from `enumerate()` in
all Pair-construction sites.  Effort: ~30 minutes including tests.

### Schema $defs/ShadowEdge — ⚠️ DIVERGENT

The schema's `$defs/ShadowEdge` has required `[src, dst, kind]` and
no `id` field.  Our `ShadowEdge` dataclass also omits `id` (matches
spec).  However, the `to_json()` output uses positional list order
(`src`, `dst`, `kind`, `ordinal`) without an explicit identifier.
This is **conformant with the schema** but the audit notes it as
DIVERGENT from the rest of the model (every other PFF construct
has an `id` field for cross-reference).  ShadowEdge is the only
unidentified record type in the model — likely intentional in the
spec, but worth flagging because RDF/JSON-LD serialization (deferred)
would need to mint blank-node ids for these.

**No code change recommended.**  The divergence is in the spec, not
in our implementation.

---

## 3. `pff.shacl.ttl` — SHACL well-formedness (15 shapes)

Status: 11 ✅ + 2 ⚠️ + 2 ⏸️.

Eleven NodeShapes are mapped to Python validators in
[src/cstz/pff.py:657](../src/cstz/pff.py#L657) `Document.validate`,
which dispatches to nine `_validate_*` helpers.  The audit traces
each SHACL shape to the validator method it lives in and the test
that exercises it.

| SHACL Shape | Status | Validator | Test |
|---|---|---|---|
| `pff:DocumentShape` | ✅ | `_validate_required_collections` | [::test_empty_doc_is_rejected](../tests/test_pff.py) |
| `pff:RankShape` | ✅ | (dataclass field types) | [::test_rank_to_json_omits_optionals](../tests/test_pff.py), [::test_dangling_rank_reference_in_patch](../tests/test_pff.py) |
| `pff:PatchShape` | ✅ | `_validate_rank_references`, `_validate_patch_references` | [::test_dangling_rank_reference_in_patch](../tests/test_pff.py), [::test_dangling_boundary_in_patch](../tests/test_pff.py) |
| `pff:ChartShape` | ✅ | `_validate_chart_references`, `_validate_patch_references` | [::test_chart_with_dangling_patch](../tests/test_pff.py), [::test_chart_with_empty_root](../tests/test_pff.py) |
| `pff:Addr0Shape` | ✅ | `_validate_addr0_segments` | [::test_addr0_without_segments_is_fatal](../tests/test_pff.py) |
| `pff:SegmentShape` | ✅ | `_validate_addr0_segments`, `_validate_pairs` | [::test_addr0_segment_unknown_rank_is_fatal](../tests/test_pff.py), [::test_segment_unknown_patch](../tests/test_pff.py), [::test_segment_without_pairs](../tests/test_pff.py) |
| `pff:PairShape` | ✅ | `_validate_pairs` | [::test_pair_unknown_chart](../tests/test_pff.py), [::test_pair_invalid_role](../tests/test_pff.py) |
| `pff:StepShape` | ⚠️ | `_validate_pairs` (kind only) | **see UniqueStepIndex below** |
| `pff:HopShape` | ✅ | `_validate_pairs` | [::test_pair_hop_unknown_boundary](../tests/test_pff.py), [::test_pair_hop_invalid_side](../tests/test_pff.py), [::test_pair_hop_port_compatible](../tests/test_pff.py) |
| `pff:Addr1Shape` | ✅ | `_validate_path_endpoints` | [::test_path1_invalid_ctor_and_endpoints](../tests/test_pff.py) |
| `pff:Addr2Shape` | ✅ | `_validate_path_endpoints` | [::test_path2_invalid_ctor_and_endpoints](../tests/test_pff.py) |
| `pff:ClassMemberShape` | ✅ | (dataclass field requirement) | [::test_classmember_to_json](../tests/test_pff.py) |
| `pff:ClassViewShape` | ✅ | `_validate_derived_views` | [::test_classview_must_be_non_authoritative](../tests/test_pff.py), [::test_classview_full_and_minimal](../tests/test_pff.py) |
| `pff:ShadowShape` | ✅ | `_validate_derived_views` | [::test_shadow_must_be_non_authoritative](../tests/test_pff.py), [::test_shadow_full_and_minimal](../tests/test_pff.py) |

### SPARQL-based well-formedness shapes (4 of them)

| Shape | Status | Notes |
|---|---|---|
| `pff:MonotoneSegmentChainShape` | ⚠️ | **DIVERGENT — encoding** |
| `pff:UniqueStepIndexShape` | ⚠️ | **DIVERGENT — encoding** |
| `pff:BoundaryPortCompatibilityShape` | ✅ | `_validate_pairs` boundary loop checks `b.has_port(hop.port)`; tested by [::test_pair_hop_port_not_on_boundary](../tests/test_pff.py) |
| `pff:UniqueSegmentRankPerAddr0Shape` | ✅ | `_validate_addr0_segments` `seen_ranks` dict; tested by [::test_addr0_duplicate_segment_rank_is_fatal](../tests/test_pff.py) |

### MonotoneSegmentChain — ⚠️ DIVERGENT (encoding)

The SPARQL constraint says: "`pff:nextSegment` must have a strictly
greater rank ordinal."  This implies segments are linked
via an explicit `pff:nextSegment` predicate (a doubly-linked-list
encoding).

**Our encoding:** segments are stored as a Python `List[Segment]`
on `Addr0.segments`.  The list position IS the linkage.
[pff.py:785](../src/cstz/pff.py#L785) `_validate_addr0_segments`
walks the list in order, comparing each segment's rank ordinal to
the previous, and emits `MonotoneSegmentChain` (fatal) on any
non-strictly-increasing pair.

This is functionally equivalent to the SPARQL constraint and
**stronger by construction**: a list cannot have arbitrary linkage,
only sequential.  But it does mean a SHACL validator running against
a Turtle export of our document would see no `pff:nextSegment`
predicate to traverse.  RDF serialization (deferred) would need to
emit those links explicitly.

**Closing the gap (if desired):** when we add the RDF export
(deferred to `pff.rdf.ttl` follow-up), emit `pff:nextSegment` triples
in segment list order.  Effort: trivial during the RDF serializer
implementation.

### UniqueStepIndex — ⚠️ DIVERGENT (encoding)

The SPARQL constraint says: "stepIndex values within a pair must be
unique."  This implies steps have an explicit numeric `pff:stepIndex`
predicate.

**Our encoding:** `Pair.route` is a `List[Step]` with positional
ordering.  No explicit `stepIndex` field.  The validator at
[pff.py:894](../src/cstz/pff.py#L894) keeps a `seen_steps` dict
keyed by the loop counter, but the check is unreachable
(`pragma: no cover`) because the loop counter cannot collide with
itself.  See the §schema/Step ⚠️ note above for the same issue.

**Closing the gap (if desired):** same as schema/Step ⚠️ — add an
explicit `index: int` field.

---

## 4. `pff.openapi.yaml` — HTTP API (4 endpoints) — ⏸️ DEFERRED ×4

No HTTP transport implemented.  All four endpoints are deferred per
the realignment plan.

| Endpoint | Status | Conformance note |
|---|---|---|
| `POST /documents` | ⏸️ | A Flask/FastAPI handler that accepts a `pff+json` body, constructs a `Document`, and returns `Document.receipt().to_json()` with the corresponding `http_status`.  Effort: ~1 hour for a single-route Flask app. |
| `GET /documents/{id}` | ⏸️ | Requires a persistence layer (in-memory dict, Postgres via `pff.sql`, etc.).  Effort depends on storage choice. |
| `POST /documents/{id}/merge` | ⏸️ | A handler that calls `Document.merge_bundle(PatchBundle.from_json(body))` and returns the resulting `DocumentReceipt`.  Effort: ~30 minutes once persistence exists. |
| `GET /documents/{id}/shadow?rank=&phase=&truncation=` | ⏸️ | Requires a Document → Shadow projector.  The legacy `agda_synth.synthesize_from_document` is the closest analog: it produces an Agda module instead of a Shadow record.  A real shadow projector would walk `Document.addresses0` and `Document.paths1` and emit `ShadowNode`/`ShadowEdge` records.  Effort: ~3 hours. |

### Schemas referenced by the OpenAPI surface

- `PffDocument` (full document body) — ✅ implemented as
  `Document.to_pff_json()`
- `PatchBundle` (incremental update body) — ✅ implemented as
  `PatchBundle.to_json()`
- `Shadow` (response body for GET /shadow) — ✅ data model
  implemented as `Shadow` dataclass; no projector emits it
- `ValidationIssue` and `DocumentReceipt` (response bodies on every
  endpoint) — ✅ implemented and `http_status` mapping conformant

The data-model side of the OpenAPI surface is fully implemented.
What's missing is exclusively the HTTP transport.

---

## 5. `pff.sql` — PostgreSQL storage (19 tables, 2 views) — ⏸️ DEFERRED ×21

No SQL backend.  All tables and views are deferred.

The `pff.sql` profile is "a normative reference implementation of
PFF persistence" with 19 tables and 2 derived views.  Conformance
requires:

- 19 PostgreSQL tables matching the spec column names and types
- Append-only triggers on 17 core tables (no UPDATE/DELETE allowed)
- Foreign key referential integrity across the linkage graph
- CHECK constraints enforcing every enum field (`role`, `ctor`,
  `kind`, `side`, `severity`, etc.)
- JSONB columns for `payload` / `meta` extensibility
- The two derived views:
  `rhpf_addr0_segment_chain` and `rhpf_addr0_route_flat`

| Table | Status |
|---|---|
| rhpf_document, rhpf_rank, rhpf_patch, rhpf_boundary, rhpf_port, rhpf_chart, rhpf_addr0, rhpf_segment, rhpf_pair, rhpf_route_step, rhpf_hop, rhpf_addr1, rhpf_addr1_premise, rhpf_addr2, rhpf_class_view, rhpf_class_member, rhpf_shadow, rhpf_shadow_node, rhpf_shadow_edge | ⏸️ |
| rhpf_addr0_segment_chain (view), rhpf_addr0_route_flat (view) | ⏸️ |

**Conformance plan (if pursued):** the most economical path is a
SQLAlchemy or raw-DDL module `src/cstz/pff_sql.py` that ports each
dataclass to a table and provides `Document.to_sql_inserts()` /
`Document.from_sql(connection)`.  Append-only is enforced by
trigger functions in a separate `pff_sql_triggers.sql` migration.
The two derived views are pure SQL — they materialize on read.
Effort estimate: ~1–2 days.

**No part of the cascade engine assumes a relational backend.**  All
state lives on the in-memory `Document` dataclass.  Adding SQL
persistence would be additive and would not require touching
`pff.py`, `pff_cascade.py`, or `pff_python_classifier.py`.

---

## 6. `pff.rdf.ttl` — RDF/OWL ontology — ⏸️ DEFERRED

No RDF emitter exists.  Conformance requires an `src/cstz/pff_rdf.py`
module that turns a `Document` into Turtle text using the namespace
`pff: <https://example.org/pff/1.0/>`.

The 19 RDF classes (`pff:Document`, `pff:Rank`, …, `pff:ShadowEdge`)
correspond exactly to our 19 dataclasses.  The ~50 properties have
matching field names on the Python side after lowercase-camelCase
normalization.  `owl:FunctionalProperty` constraints (e.g.,
`pff:ordinal` is functional) are already enforced by Python type
annotations (each field is `int`, not `List[int]`).

**Conformance plan (if pursued):** ~200 lines of Python that walks
each `Document.<collection>` and emits Turtle triples.  Each
dataclass `to_json()` already produces a flat dict that maps
1:1 to RDF property assertions; the rdf serializer just rewrites
keys to `pff:` URIs and emits `<subject> <predicate> <object> .`
triples.  Effort: ~3 hours.

---

## 7. `pff.context.jsonld` — JSON-LD context — ⏸️ DEFERRED

No JSON-LD emitter exists.  The context file defines a namespace
prefix and 50+ property term mappings (with `@type: @id` for object
references).  Conformance requires a `Document.to_jsonld()` method
that wraps the existing `to_pff_json()` output with `@context`,
`@type`, and `@id` keys.

**Conformance plan (if pursued):** trivial wrapper on top of
`to_pff_json()` once the namespace mapping is settled.  Effort: ~1
hour.  The existing `to_pff_json()` keys already match the context
file's term names (camelCase), so the rewriter is mostly a
"prefix every key with `pff:` if needed" transformation plus
`@id` injection on the identifier fields.

---

## 8. `pff.amr.md` — AMR (Penman) projection — ⏸️ DEFERRED

No AMR exporter exists.  The AMR profile is a *presentation*
projection, not a storage profile, so it's the lowest-priority
deferred item.  Conformance requires a `Document.to_amr_penman()`
method that emits:

```
(d / pff-document
   :hasRank (r / rank :ord 0)
   :hasPatch (p / patch :id "p0" :phase "ingest")
   :hasAddr0 (a / addr0 :id "addr0-0"
                :hasSegment (s / segment
                                :hasPair (pr / pair :role "principal")))
   :hasPath1 (e / path1 :ctor "glue" :src "addr0-0" :dst "addr0-1"))
```

**Conformance plan (if pursued):** ~150 lines walking the document
tree and emitting Penman s-expressions.  Round-trip back into a
Document is harder (Penman parsing is non-trivial) and may be
explicitly out of scope even within AMR conformance.  Effort:
~2 hours one-way; ~1 day round-trip.

---

## Recommended follow-ups

Items that the audit thinks are worth closing, in priority order:

1. **Schema `Step.index` field** (closes 2 ⚠️ items: schema $defs/Step
   and SHACL UniqueStepIndex).  ~30 minutes including a positional
   `enumerate()` injection in all Pair-construction sites.  The
   payoff is round-trippability through a real SHACL validator.

2. **`MonotoneSegmentChain` `pff:nextSegment` linkage** (closes 1 ⚠️
   item, only if RDF export is implemented).  Trivial during the RDF
   serializer work; not worth doing standalone.

3. **JSON-LD wrapper** (`pff.context.jsonld`, ~1 hour).  Cheapest
   serialization to add and the most reusable for downstream consumers.

4. **RDF/Turtle emitter** (`pff.rdf.ttl`, ~3 hours).  Enables real
   SHACL validation against the spec, which would reduce the audit's
   ⚠️ markers to 0.

5. **OpenAPI HTTP wrapper** (`pff.openapi.yaml`, ~1 hour for a single
   in-memory route).  Makes cstz a conforming PFF service, even
   without persistence.

6. **PostgreSQL backend** (`pff.sql`, ~1–2 days).  Highest cost,
   highest leverage if multi-process or persistent storage is
   wanted.

7. **AMR projection** (`pff.amr.md`, ~2 hours one-way).  Lowest
   priority; presentation profile only.

Items that should stay deferred indefinitely:

- None.  Every deferred item has a coherent conformance path.  The
  PFF stack is in good shape and can grow into full conformance one
  serializer at a time without restructuring the data model.

## Audit verification

- **Cross-reference check:** every test name cited in this report
  was confirmed via `pytest --collect-only` against
  `tests/test_pff.py` (64 tests collected, all citations match) and
  `tests/test_pff_cascade.py` (63 tests collected).
- **Schema spot-check:** a populated `PFFCascadeEngine` Document
  with 2 observations + 1 streaming glue was emitted via
  `to_pff_json()` and manually compared against `pff.schema.json`
  required-fields lists for `Document`, `Rank`, `Patch`, `Chart`,
  `Addr0`, `Segment`, `Pair`, `Step`, and `Addr1`.  All required
  fields present; no schema-forbidden extra keys.
- **Test suite:** to be re-run after this audit is committed; the
  expectation is 698 tests still pass since this audit changes no
  source code, only adds this report.
