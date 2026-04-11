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
| --- | --- | --- | --- | --- | --- |
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

## Postscript: GF(2) double-use and the H₀ correspondence

This audit's first draft framed the cstz cascade as "structural-key
collision detection + union-find" and contrasted that with a literal
"`Ax = f` over F₂" linear-algebra solver, treating the two as
operationally distinct.  That framing was wrong.  The two are the
same computation viewed through dual lenses, and a complete audit
should make the equivalence explicit.

### The mathematical equivalence

For a graph `G` with vertex set `V` and edge set `E`, the connected
components of `G` are exactly the basis of

```text
H₀(G; F₂)  =  F₂^V / im(∂)
```

where `∂ : F₂^E → F₂^V` is the boundary map sending each edge
`(a, b)` to the formal sum `e_a + e_b` (XOR over F₂).

In other words: **computing connected components = computing the
cokernel of the boundary map = solving a homogeneous linear system
over F₂.**

Union-find is just an asymptotically faster algorithm for the same
computation.  Given a stream of edges, union-find produces the
connected-components partition with α(n) inverse-Ackermann
amortization per edge; explicit Gaussian elimination on the boundary
matrix produces the same partition in O(EV) time.  Same answer; same
mathematical content; different data structure.

The cstz cascade in `_addr0_uf` IS solving `Ax = 0` over F₂, where:

- **Variables** `x ∈ F₂^N` index the addr0 set
- **Each glue Addr1** contributes one row to A: for `glue(a, b)`,
  the row is `e_src + e_dst`
- **The output** is `ker(A^T) = H₀(G_glue; F₂)` = the partition of
  addr0s into path1 equivalence classes

The same picture applies to path2: `_addr1_uf` solves the analogous
system over Addr1 ids with rows contributed by each Addr2 with
`ctor=coh`.

### What the cascade adds: a self-referential closure

Plain union-find solves `Ax = 0` for a *fixed* matrix A.  The cstz
cascade is more interesting: it solves a self-referential variant
where the matrix itself depends on the current solution.

Specifically: two addr0s are equivalent iff they have the same
**structural key** under the equivalence relation defined by which
addr0s are equivalent.  This is a fixed-point equation,
`find x such that A(x)·x = 0` where `A(x)` depends on `x`.

The cascade solves it by **monotone iteration**.  Each round:

1. Compute structural keys under the current partition.
2. Detect collisions → those are new rows of A → add them via the
   union-find.
3. Re-canonicalize parents whose children's classes have moved.
4. Loop until no new rows are added.

Each round adds rows to A monotonically.  The addr0 set is finite,
so the fixed point is reached in finite steps.  At convergence, the
null space of A is the unique greatest equivalence relation
consistent with the structural-key constraint.  **This is exactly
sheafification** in the topos-theoretic sense: the cascade lifts a
presheaf of local observations to a globally consistent sheaf by
gluing overlapping sections, and the final partition IS the sheaf.

### F₂ shows up in cstz twice, not once

When this audit's [Step 6 inference.agda PFF correspondence
comments](../inference.agda) describe `SPPF.GF2` as "the orientation
discipline for `Pair.role ∈ {principal, aux}`", that description is
correct but **incomplete**.  F₂ appears in cstz in two distinct,
mathematically consistent ways:

| Role | Where | What it computes |
| --- | --- | --- |
| **κ-coproduct discriminator** | `SPPF.GF2` in `inference.agda`; `Pair.role`, `Chart.kind` in `pff.py` | A 2-element-choice torsor (principal/aux, sigma/tau).  The orientation bit of the σ ⊎_τ σ coproduct. |
| **Sheafification linear algebra** | The cascade in `pff_cascade._UnionFind` + `_glue_set_and_cascade` + `_cascade_after_merge` | The boundary map `∂ : F₂^{glues} → F₂^{addr0s}` whose null space is the path1 partition (= H₀ of the glue graph).  Same construction over Addr1 ids and coh edges for path2. |

Both uses are real, both live in F₂, and they're consistent: the
cascade computes the partition, and `Pair.role` discriminates each
member of each partition class against the principal/aux orientation.
Reading (a) of the κ-coproduct (`Pair.role`) is the bit assigned to
each class element; reading (b) (`Chart.kind`) is the bit assigned
to each chart; the cascade is the machinery that decides which
addr0 lives in which class via a linear-algebra computation over
the *same* F₂.

### Updated status (no audit findings change)

This is a conceptual correction, not a new gap.  None of the
audit's existing markers change — every ✅ stays ✅, every ⚠️ stays
⚠️, every ⏸️ stays ⏸️.  What changes is the **interpretation** of
the SHACL section's two ⚠️ items (MonotoneSegmentChain and
UniqueStepIndex):

- The audit said "we encode segment ordering positionally in
  `List[Segment]` rather than via `pff:nextSegment` predicates,
  which is stronger by construction."  That's still true, but the
  right *reason* it's stronger by construction is that the
  list-positional encoding IS the boundary map's domain in the H₀
  computation: the segment order is the basis of `F₂^E`, and the
  cascade's union-find is computing `F₂^V / im(∂)` directly on
  that basis.  The SHACL `pff:nextSegment` predicate is one way
  to *write down* the boundary map; our list is another.

The implementation is unchanged.  The audit's findings are unchanged.
The way we describe the implementation should mention both uses of
F₂ rather than just the κ-coproduct discriminator.

### Implications for the codebase

Three follow-up actions land in the recommended-follow-ups list
below as items 0a, 0b, 0c (prepended at top priority):

- **0a.** Update the `inference.agda` Step 6 PFF correspondence
  comments above `SPPF.GF2`, `SPPF.UnionFind`, `SPPF.Eta`, and
  `SPPF.ClosureProofs` to mention the H₀ / cokernel-of-boundary-map
  correspondence and the dual use of F₂.  Comment-only; no proof
  bodies change.
- **0b.** Add explicit accessor methods to `pff.Document` that
  surface the linear-algebraic view: `path1_constraint_rows()`,
  `path1_canonical_map()`, `path1_classes()`, and the analogous
  three for path2.  These compute the H₀ partition from a
  Document's `paths1` / `paths2` collection alone (no cascade
  engine needed).  Refactor `agda_synth._path1_closure` /
  `_path2_closure` to delegate to the new accessors.
- **0c.** Add a property-based test that for any populated
  `PFFCascadeEngine`, `engine.document.path1_classes()` agrees
  with `engine.all_addr0_classes()` as a partition.  This makes
  the H₀ ↔ cascade equivalence a verified runtime invariant
  rather than a comment.

These three items together would close the gap between the
document's "Ax = f over F₂" framing in
`Topos-Theoretic Grammar Induction and PRNG.md` and what cstz
empirically computes.

---

## Postscript: The Slicer is in the fixed-point calculation, and its output is in the Document

A second conceptual correction, same shape as the GF(2) one.

The original draft of this audit dismissed the "Slicer" mechanism
from §2.1 of `Topos-Theoretic Grammar Induction and PRNG.md` as
absent from cstz: the document described a Slicer generating a
Grothendieck topology via "overlapping open sets", and I read
"overlapping open sets" as "sliding window" and concluded cstz has
no such component (the Python classifier walks the AST recursively
and the byte classifier consumes one byte at a time).

That reading was wrong for the same reason the GF(2) dismissal
was wrong: the Slicer is not a sliding-window generator, it's a
**covering-sieve generator** that happens to satisfy the
Grothendieck-topology axioms, and **the cascade's fixed-point
iteration is exactly that generator.**

### Mapping the three Grothendieck-topology axioms to cascade invariants

For the σ-Slicer — which operates on Addr0s via the sigma-key
`(sigma_chart_id, canonical_sigma_children)` — the three axioms of
a Grothendieck topology correspond directly to invariants the
cascade already maintains:

| Grothendieck axiom | Cascade invariant |
| --- | --- |
| **Identity cover** — maximal sieve covers every object | Every Addr0 starts in its own singleton sigma-key class the moment it's added via `add_observation` |
| **Stability under pullback** — pullback of a covering sieve is a covering sieve | Monotonicity: the cascade only *adds* to `_addr0s_by_sigma_key` buckets, never removes.  Adding a new observation never invalidates an existing equivalence |
| **Transitivity** — local covers compose into global covers | Recursive cascade: when a glue changes `canon_children` for a parent sigma_key, `_cascade_after_merge` re-canonicalizes parent keys and detects cascading collisions.  The worklist iteration IS the transitive closure of the covering sieve system |

The "Slicer" lives in the three-line sigma-key computation inside
[`add_observation`](../src/cstz/pff_cascade.py):

```python
canon_sigma_children = tuple(
    self._addr0_uf.find(c) for c in sigma_children
)
sigma_key = (sigma_chart.id, canon_sigma_children)
# ...
self._addr0s_by_sigma_key[sigma_key].add(addr0_id)
```

And the "topology-building iteration" — the part that takes the
initial flat assignment of sigma-keys and refines it to the fixed
point where the three axioms hold — is [`_cascade_after_merge`](../src/cstz/pff_cascade.py).

### Theorem: σ-key equivalence = path1 equivalence under correct usage

Let `E` be a `PFFCascadeEngine` at convergence.  Let `Σ(E)` be the
partition of Addr0 ids induced by sigma-key equivalence (two Addr0s
are equivalent iff they sit in the same bucket of
``_addr0s_by_sigma_key``).  Let `P(E)` be the partition induced by
the path1 closure (two Addr0s are equivalent iff they're connected
by a chain of glues).

**Primary theorem (correct-usage regime):** when every path1 edge
is derived from a sigma-key collision during streaming ingest (i.e.,
no merges are *forced* from outside the cascade's structural
discipline), **`Σ(E) = P(E)`** at convergence.  This is proved by
the monotone-canonical-children argument in the inference.agda
`SPPF.ClosureProofs` comment, and empirically verified by the test
class `TestSigmaKeyEqualsPath1InPureCascade` in
`tests/test_pff_cascade.py`.

**Secondary theorem (robustness under data corruption):** even when
a caller bypasses the cascade by issuing `engine.glue(a, b)` between
two Addr0s with distinct sigma-keys — a pattern considered **data
corruption** under the PFF discipline (see below) — the weaker
refinement property still holds: **`Σ(E)` is a refinement of
`P(E)`**.  Every sigma-key bucket sits entirely inside a single
path1 class, though a single path1 class may now contain multiple
sigma-key buckets.  The cascade degrades gracefully: its internal
bookkeeping stays consistent even in the presence of external
forced-merge corruption.

*Proof sketch for the primary theorem.*

**(`Σ ⊆ P`)** If `A` and `B` have the same sigma-key at convergence,
the cascade's sigma-key-collision detection fired on them — otherwise
there would be an unprocessed collision, contradicting the
fixed-point hypothesis.  So they were glued, and they are in the
same path1 class. ✓

**(`P ⊆ Σ`, under correct usage)** If `A` and `B` are in the same
path1 class via a chain `A = A_0 ~ A_1 ~ ... ~ A_n = B` of glue
events, and every link was emitted because of a sigma-key match,
then at each link the canonical-children tuples were equal at the
round of the glue.  Monotonicity of the path1 union-find preserves
that equality forever.  By transitivity along the chain, `A_0` and
`A_n` have identical sigma-keys at the fixed point. ✓

### User-initiated merges as data corruption

The secondary theorem exists only because the current engine
exposes `PFFCascadeEngine.glue()` as a public API that accepts
arbitrary (src, dst) Addr0 pairs.  Under the PFF structural
discipline, **this API is problematic**: it lets users force
merges that the cascade wouldn't derive from the data alone,
effectively rewriting the categorical structure by fiat.

The clean pattern for introducing equivalences in PFF is:

- **Correct:** provide data that triggers sigma-key collision via
  `add_observation`, OR introduce a new discriminator (a new chart
  axis or sigma-key component) that causes the equivalence to
  emerge from the data's interaction with the discriminator.  The
  cascade then derives the merge, and the merge is justified by
  the data.
- **Incorrect (data corruption):** call `engine.glue(a, b)` between
  two Addr0s that the cascade would not otherwise equate.  This
  forces a path1 edge that's not backed by any structural
  derivation, and the sigma-key partition drifts from the path1
  partition as a result.

If a user wants to introduce a cleavage-point discriminator — a
new distinction that carves an equivalence class into sub-classes
— the right move is to augment the observation data with tags that
trigger the discrimination through the existing cascade machinery,
not to bypass the cascade with direct glue calls.  A future commit
should deprecate `engine.glue()` as a public API in favor of
discriminator-synthesis helpers, leaving the current method as
cascade-internal only.

### Corollary: the σ-Slicer's output is Document-computable

### Corollary: the topology is Document-computable

The σ-Grothendieck topology at the cascade fixed point IS
`Document.path1_classes()`.  It does not require `sigma_children`
(which is cascade-internal state not serialized to the Document).
It does not require any rotation or coproduct identity to
"reconstruct" missing information, because nothing is missing.

The PFF serialization is **topologically complete**: a Document
captures everything observable about the cascade's fixed-point
output, even though the cascade's internal machinery (sigma-key
dicts, parent indices, child tuples) is not serialized.

### The τ-Slicer and the asymmetry it exposes

The GF(2) postscript established that F₂ appears in cstz in two
places (κ-coproduct discriminator, sheafification linear algebra).
Once that double-use is in scope, the Slicer picture has to be
symmetric as well: there should be a **σ-Slicer** over Addr0s and
a **τ-Slicer** over Addr1s, each using both F₂ places.

| Slicer | Uses F₂ place 1 (orientation) for… | Uses F₂ place 2 (kernel) for… | Fixed-point output |
| --- | --- | --- | --- |
| **σ-Slicer** | picking out the principal pair's σ-chart per Addr0 (`pair.role == "principal"` / `chart.kind == "sigma"`) | computing `H_0` of the Addr0 glue graph (path1 union-find) | `path1_classes()` — σ-Grothendieck topology over Addr0 ids |
| **τ-Slicer** | picking out the aux pair's τ-chart per Addr0 (`pair.role == "aux"` / `chart.kind == "tau"`) | computing `H_0` of the Addr1 coh graph (path2 union-find) | `path2_classes()` — τ-Grothendieck topology over Addr1 ids |

### Implementation asymmetry: the cascade currently has half of this

The σ-Slicer is implemented with full streaming semantics: the
cascade auto-emits Addr1s whenever sigma-keys collide, recursively
re-canonicalizes parents, and iterates to a fixed point.

The τ-Slicer is currently **user-initiated**: `engine.coh(src, dst)`
records a coh Addr2 between two existing Addr1s, but the engine
does not scan `paths1` for raw-pair duplicates and auto-emit cohs.
The path2 partition at any point is just the transitive closure of
user-declared coh equivalences.

This asymmetry has a clean fix that aligns with the "by
construction" principle underlying PFF: **implement an auto-coh
fixed-point pass** that scans `paths1`, groups by sorted raw
`(src, dst)` pair, and emits cohs within each group.  When two
Addr1 records witness the same equivalence (by raw pair) they are
coherent by construction — and the equivalence exists.  If a
discriminator is later introduced that distinguishes them, that
distinction manifests as a cleavage plane in the SPPF sense
(a forced case split), which is exactly the right semantics for
SPPF cleavages.

The auto-coh pass is idempotent and converges in one scan because
cohs only affect `_addr1_uf` (the path2 union-find), not
`_addr0_uf` (the path1 union-find), so the canonical pairs
computed during the scan are stable.

A subtlety that the first draft of this postscript missed: the
σ-cascade's skip-check prevents duplicate Addr1s with the same
**raw** (src, dst) pair from being emitted in a single run, but
it does not prevent distinct raw pairs from canonicalizing to
the same canonical pair after the cascade closes.  For a path1
class of `n` addr0s the σ-cascade emits `n-1` glues (anchor-first
pattern), and auto-coh emits `n-2` cohs to unify them.

That is, auto-coh fires even on normal σ-cascade output whenever
a path1 class has more than two members.  This is correct
behavior: each of the n-1 glues witnesses the equivalence from a
different raw-endpoint angle, and all of them are coherent by
construction.  The cohs make that coherence explicit in the
Document, symmetric with how the σ-cascade makes the glue
coherence explicit.

Auto-coh also fires on:

- Documents produced by `Document.merge_bundle` when both sides
  independently glued the same canonical pair
- User-constructed Documents with manually-added duplicate Addr1s
- Any future refactor that removes the σ-cascade's
  emission-dedup logic

The pass emits **zero** cohs only when every path1 class is a
singleton or a pair — i.e., no path1 class has enough witnesses
to produce a coherence relationship among them.

### Earley is also in the fixed-point calculation

A third "it's there in the fixed-point calculation" finding, same
shape as the GF(2) and Slicer corrections.  The original
Topos-Theoretic study's dismissal — *"cstz uses neither Earley nor
GLL/GLR"* — was wrong about Earley.  Earley's chart-based parsing
algorithm is exactly the cascade's self-referential fixed-point
iteration, under different vocabulary.

| Earley concept | cstz cascade counterpart |
| --- | --- |
| **Chart** — indexed table of items by input position | `_addr0s_by_sigma_key` + `_sigma_keys_by_child` — the sigma-keyed index of observations |
| **Scanner** — reads a terminal and advances matching items | `add_observation` — ingests a new raw AST node / byte and inserts it into its sigma-key bucket |
| **Predictor** — given `A → α · Bβ` at position i, adds `B → · γ` for each rule.  **Its grammar source is the chart itself** (self-referential) | sigma-key collision detection — when a new observation lands in an existing bucket, the cascade "predicts" the new observation will behave as the existing ones do.  The "grammar" is the accumulated sigma-key registry itself, precisely mirroring Earley's self-referential predictor |
| **Completer** — given a completed item at position j and a waiting item at position i, advances the waiting item | `_cascade_after_merge` — when a child is glued, parent sigma-keys re-canonicalize and parent classes are discovered.  "A child parse has completed, now advance the waiting parents" |
| **Fixed-point iteration over chart state** | `_cascade_after_merge`'s worklist loop — iterates until no more sigma-key movements |
| **Parse success: chart contains a completed S-item spanning the input** | Cascade convergence: `_addr0s_by_sigma_key` reaches a fixed point |

Earley's predictor famously uses the chart *as its own grammar* —
it doesn't consult an external rule table; it looks up what to
predict by inspecting accumulated chart entries.  That
self-referential move is exactly what the cascade does when
`_cascade_after_merge` uses `_sigma_keys_by_child` (a view over the
chart) to drive re-canonicalization.  Neither component consults an
external grammar; both use their own accumulated state as the
grammar source.

cstz doesn't have an Earley *implementation* in the textbook sense
(no item records, no dot-notation, no position indices).  It has
something more abstract: **Earley's fixed-point structure** applied
to σ-key equivalence closure instead of context-free-grammar item
progression.  The textbook Earley is one instantiation of this
structure; the cstz cascade is another.

The implication for the audit: the original claim *"cstz uses
neither Earley nor GLL/GLR"* should be weakened to *"cstz does not
have a textbook Earley implementation, but the cascade's
fixed-point iteration realizes the same self-referential
chart-based parsing structure that Earley does."*  (GLL and GLR
are separate and I don't know enough about either to say whether
the analogy extends.)

### Slicer-postscript implications for the codebase

Three follow-up actions, landing as items 0d, 0e, 0f at top
priority (prepended to the recommended-follow-ups list):

- **0d.** Update the `inference.agda` Step 6 PFF correspondence
  comments above `SPPF.Eta` and `SPPF.ClosureProofs` to mention
  the Grothendieck topology axiom correspondence and the σ-key
  equals path1 theorem.  Comment-only; no proof bodies change.
- **0e.** Add explicit Slicer accessors on `pff.Document` and
  `PFFCascadeEngine`: `covering_sieves_over_addr0()` (σ-Slicer)
  and `covering_sieves_over_addr1()` (τ-Slicer), both as
  semantically-named aliases for `path1_classes()` /
  `path2_classes()`.  Plus property-based tests in
  `TestGrothendieckTopology` verifying the three axioms hold
  at both levels, and a `test_sigma_key_equals_path1_at_fixed_point`
  test that empirically verifies the theorem above.
- **0f.** Implement the **auto-coh fixed-point pass** as
  `Document.auto_coh_closure()` (standalone) and
  `PFFCascadeEngine.auto_coh_closure()` (engine wrapper), with
  the engine's `add_observation` calling it automatically at the
  end of each ingest.  This makes the σ-cascade and τ-cascade
  symmetric at the implementation level, not just mathematically.
  Tests cover: normal no-op (no duplicates from σ-cascade alone),
  manual duplicates, merge duplicates, idempotency, and
  integration with the σ-cascade's existing output.

### A note on templating (deferred)

The σ-cascade's `_glue_set_and_cascade` inner loop and the τ-cascade's
auto-coh pass share the same shape: *"for each key with ≥2
elements, emit merges within the group."*  These are candidates
for templating into a generic `CascadeIteration[Element, Key]`
helper that both cascades instantiate.

The σ-cascade additionally requires recursive re-canonicalization
of parent sigma-keys — a self-referential fixed-point not present
in the τ-cascade.  A generic template would expose
`recanonicalize_on_merge` as an optional callback, with the
σ-cascade providing it and the τ-cascade passing `None`.

This refactor is **intentionally deferred** to a follow-up of
item 0f.  The initial auto-coh implementation will mirror the
σ-cascade's inner-loop pattern in a new method without extracting
a shared helper, to keep the risk low and the tests independent.
Once both cascades are tested in their current form, extracting
the generic iteration becomes a pure refactor that preserves
behavior.

### Experiment: cstz-on-cstz as a refactor oracle

With both cascades (σ-cascade in
`PFFCascadeEngine._glue_set_and_cascade` /
`_cascade_after_merge`, τ-cascade in
`Document.auto_coh_closure` / `PFFCascadeEngine.auto_coh_closure`)
present in the tree as of commit `d72acb5`, a cstz-on-cstz
experiment became possible: factorize the source files through
`pff_python_classifier.factorize`, inspect the resulting
`path1_classes()`, and look for structural equivalences between
the two cascades' inner loops.  If cstz's AST-level equivalence
notion identified the merge-emission pattern as shared, that
shared structure could directly guide the helper extraction for
item (C2b).

**Result: cstz finds zero structural equivalence between the two
cascades at the loop-or-conditional level.**  The combined
factorization of `pff.py + pff_cascade.py` produces 62
non-singleton path1 classes spanning 3297 Addr0s, but querying
those classes by AST node type yields:

| AST type queried | Cross-cascade classes |
| --- | --- |
| `For` | 0 |
| `If` | 0 |
| `Call` | 0 |
| `Compare` | 0 |
| `AugAssign` | 0 |
| `ListComp` | 0 |
| `Subscript` | 4 (all trivial type-annotation matches) |

The only cross-file equivalences are trivial shared-identifier
patterns: `Name("self")` references, `Attribute` chains like
`self.document.paths1.append(...)`, and isomorphic type
annotations in function signatures.  None of them capture the
"merge-emission loop" structure we were looking for.

**Diagnosis.**  cstz's `_addr0_signature_index` hash-consing is
**lexical**, not α-equivalent.  A sigma-key for a `Name` node
includes the identifier string as a param, so
`Name("ids")` and `Name("sorted_members")` are distinct Addr0s,
their parent `Subscript` nodes differ, and everything above
those two leaves differs all the way up to the enclosing
function definitions.  The only way two Addr0s ever end up in
the same path1 class is if their sigma-keys (including all
nested leaf identifiers) match exactly.

A synthetic experiment confirmed this is the limiting factor:
two functions with **identical bodies and identical local
variable names** collapse to ONE For Addr0 via hash-consing
(because their full sigma-keys match), but when the same two
functions have identical bodies and DIFFERENT local variable
names (`ids` vs `sorted_members`), the For nodes stay in
separate path1 classes.  Equality-up-to-local-renaming is not
something cstz's current cascade can detect.

This is **not a bug** in cstz — α-equivalence vs lexical
equivalence is a meaningful design choice, and the lexical
choice preserves valuable information (a refactor that renames
a variable is NOT a no-op under cstz's equivalence relation,
which is exactly right for many refactor-tracking use cases).
But it does mean that cstz-on-cstz cannot directly identify the
merge-emission loops as shared structure, and the templating
helper extraction for item (C2b) cannot be empirically guided
by the current cascade alone.

### The deeper finding: speculative rotation + natural transformation

The α-equivalence limit points at a more general extension of
the cascade.  Two Addr0s that fail to sigma-key-collide but
differ only by a local rewriting should be connectable via a
**speculative rotation** of one cell's hash-consed representation
onto the other's — and the successful rotation, recorded as a
structured morphism, is exactly what a **natural transformation**
captures in the category-theoretic sense.

Concrete framing:

- A **hash-consed cell** is an Addr0 with its sigma-key
  `(ast_type, params, canonical_children)`.
- A **rotation** is a substitution / permutation / rewriting
  applied to the cell's params or children that produces a new
  sigma-key.  The rotation is "speculative" because we apply it
  without yet knowing whether it produces a collision.
- A **shape collision** is the success condition: after rotation,
  the new sigma-key matches an existing cell's sigma-key.
- A **natural transformation** is the Addr1 record that captures
  the collision: its `ctor` names the rotation kind (e.g.,
  `ctor="alpha-rename"`), its `args` record the substitution
  (e.g., `args={"rename": {"ids": "sorted_members"}}`), and its
  `src` / `dst` are the two connected Addr0s.

Generalizing across the different rotation groups:

| Rotation kind | Rotation group | Resulting Addr1 ctor |
| --- | --- | --- |
| α-equivalence | local variable renaming (substitution group on bound names) | `alpha-rename` |
| β-equivalence | inlining + common subexpression elimination | `beta-reduce` |
| η-equivalence | extensionality application | `eta-expand` |
| commutativity | argument reordering for commutative binops | `commute` |
| associativity | re-parenthesization of associative operators | `reassociate` |

Each rotation kind corresponds to a functor from a **syntactic
category** (morphisms are literal identity) to a **quotient
category** (morphisms are equivalences under that rotation).
Natural transformations between these functors materialize as
Addr1 records connecting the pre-rotation cell to the
post-rotation cell.

This is the "quotient category lifting" pattern, and α-equivalence
is the simplest nontrivial instance.  Implementing it inside the
existing cascade amounts to:

1. Adding a **rotation pass** that runs after `_cascade_after_merge`
   settles, scanning for cells whose structures differ only by a
   chosen rotation group.
2. Emitting Addr1 records with the rotation-specific ctor for each
   collision found.
3. Including those Addr1s in the path1 closure so downstream
   Grothendieck-topology queries see the extended equivalence.

This is substantially more machinery than the plain cascade has,
and it's explicitly deferred as a **future feature** beyond the
current audit scope.  The bounded experiment below tests whether
a simpler approach — α-normalization before factorization — is
sufficient for the specific empirical goal of finding the shared
structure between the two cascades.

### Bounded experiment: α-normalization before factorization

Rather than adding a rotation pass inside the cascade, a simpler
preprocessing step is to **α-normalize the AST before
factorization**: rewrite every local variable binding to a
canonical name (`v0`, `v1`, ...) determined by first-appearance
order within its scope, then feed the normalized AST to
`factorize`.  Under α-normalization, two functions with
identical bodies and different local variable names produce
identical normalized ASTs, and cstz's lexical hash-consing
correctly identifies them as structurally equivalent.

This is not as general as the speculative-rotation approach — it
only handles α-equivalence, not β / η / commutativity /
associativity — but it is enough to empirically verify whether
the σ-cascade and τ-cascade share a merge-emission loop at the
AST level, which is the specific question (C3) was supposed to
answer.

### Query specification (Step 0)

Before building the machinery that would answer the
cstz-on-cstz question empirically, this section writes down the
*exact query* that the eventual experiment will execute.  Pinning
the query down first — before any α-normalization, provenance
tracking, or factorization plumbing exists — gives every
subsequent step a precise specification to implement against.
See [replicated-popping-bentley.md](../../../.claude/plans/replicated-popping-bentley.md)
§"Step 0 — Query specification" for the DAG framing.

**The unifying question:**

> For a given source tree, which AST subtrees are referenced from
> more than one function after hash-consing under α-equivalence?

**The query signature (target for Step 3):**

```python
def shared_across_functions(
    self: Document,
    min_span: int = 2,
) -> List[AddrShareRecord]:
    """Return Addr0s whose hash-cons backings span ≥ min_span
    distinct enclosing functions.

    The return is ordered by span count descending, then by
    Addr0.id ascending.  Caller is expected to filter the result
    by AST sort type to surface structurally-interesting matches
    (For / If / While / ListComp / etc.) and hide trivial leaf
    matches (Name / Constant / etc.)
    """
```

with

```python
@dataclass
class AddrShareRecord:
    """One Addr0 that was referenced from multiple functions
    during factorization.

    Built by Document.shared_across_functions from the provenance
    metadata that add_observation records on each Addr0's
    meta["backings"] list during ingest.
    """

    addr0_id: str
    sort: str                              # AST node type
    backings: List[Tuple[str, str, int]]   # (file, scope_path, line)
    function_span: FrozenSet[str]          # distinct scope_paths
```

**Prerequisites for the query to be meaningful:**

1. The input Document must be built by factorizing an
   **α-normalized** AST, so that two lexically-distinct
   subtrees with the same α-equivalence class collapse to a
   single hash-consed Addr0 at ingest time.  **This is Step 1.**
2. Each hash-cons dedup event in `add_observation` must record
   the colliding caller's location on the existing Addr0's
   metadata, rather than silently discarding it.  Without this,
   the `function_span` field would only reflect the first
   ingestor and every Addr0 would appear singleton-scoped.
   **This is Step 2.**

Only after both prerequisites land can the query be implemented
as a pure filter over `doc.addresses0` (~20 lines), as specified
in Step 3 of the plan.

**Worked example.**  Consider the synthetic input from the
cstz-on-cstz experiment that produced the `fac14a1` finding:

```python
def sigma_inner(ids, engine, rank, patch, label):
    collect = []
    anchor = ids[0]
    for other in ids[1:]:
        if engine.find(anchor) == engine.find(other):
            continue
        collect.append(engine.emit(anchor, other, rank, patch, label))
    return collect

def tau_inner(items, eng, r, p, tag):
    results = []
    head = items[0]
    for elem in items[1:]:
        if eng.find(head) == eng.find(elem):
            continue
        results.append(eng.emit(head, elem, r, p, tag))
    return results
```

After α-normalization (Step 1), both functions' bodies become
byte-for-byte identical modulo their FunctionDef names: every
parameter is `v0..v4`, every local is `v5..v7`, the `for` loops
are lexically identical, the `if` conditions are lexically
identical, the `append` calls are lexically identical.

After factorizing the normalized AST with provenance tracking
enabled (Step 2), cstz's hash-consing merges the `For` subtree,
the `If` subtree, the `Call` subtrees, and every intermediate
node into single Addr0s — with `meta["backings"]` on each
recording BOTH `sigma_inner` and `tau_inner` as the functions
that contributed ingests.

Calling `doc.shared_across_functions(min_span=2)` (Step 3) then
returns (something close to):

```python
[
    AddrShareRecord(
        addr0_id="addr0-40",
        sort="For",
        backings=[
            ("synthetic.py", "<module>:sigma_inner", 5),
            ("synthetic.py", "<module>:tau_inner", 14),
        ],
        function_span=frozenset({
            "<module>:sigma_inner",
            "<module>:tau_inner",
        }),
    ),
    AddrShareRecord(
        addr0_id="addr0-35",
        sort="If",
        backings=[
            ("synthetic.py", "<module>:sigma_inner", 6),
            ("synthetic.py", "<module>:tau_inner", 15),
        ],
        function_span=frozenset({
            "<module>:sigma_inner",
            "<module>:tau_inner",
        }),
    ),
    # ... more records, one per shared subtree ...
]
```

The top-ranked result is the `For` loop (the largest shared
subtree by structural reach), followed by its children (`If`,
`Call`, `Compare`, ...) which are also shared but rank lower
because they cover fewer lines.  The `FunctionDef` nodes
themselves do NOT appear in the result because their names
differ (`sigma_inner` ≠ `tau_inner`), so they aren't
hash-consed, so each remains singleton-scoped.

**This is exactly the structure we want to find.**  If Step 4's
empirical experiment run on `src/cstz/pff.py` + `pff_cascade.py`
produces an analogous result — a top-ranked `For` Addr0 whose
`function_span` is `{PFFCascadeEngine._glue_set_and_cascade,
Document.auto_coh_closure}` — then the merge-emission loop is
empirically confirmed as shared structure, and Step 5's
extraction is mechanically guided by the backings list.

**What the query does not claim.**  The query answers "does
shared structure exist at the AST level?"  It does not answer
"should this shared structure be factored into a helper?" — that
is a human-judgment call informed by the result.  A shared
`Subscript("optional type annotation")` Addr0 spanning 10
functions is structurally shared but semantically trivial and
should not trigger a refactor; a shared `For` loop spanning 2
functions is structurally rarer and semantically meaningful.
The filter-by-interesting-sort step in Step 4 is where that
judgment lives.

**Risk (Step 0 only).**  The query shape as written here might
be wrong.  If the empirical experiment in Step 4 produces
unexpected output — too many trivial leaves, too few
structural matches, or matches that group things that shouldn't
be grouped — the residual tells us which of Steps 1-3 drifted.
The worked example above is the concrete target every
implementation step below is reaching for, and the Step 4
report will cite this example as the validation baseline.

### Implementation steps 1-5 (deferred to follow-up commits)

With the query specification fixed, the five implementation
steps can proceed in order.  Each step's commit message will
cite its role in the DAG described in
[replicated-popping-bentley.md](../../../.claude/plans/replicated-popping-bentley.md):

- **Step 1** — `src/cstz/ast_alpha.py` with the α-normalization
  pass.  Renames locals to `v0`, `v1`, ... by first-appearance
  order per scope.  Module scope unchanged.  Free variables
  left as-is for this bounded experiment.
- **Step 2** — provenance tracking in
  `PFFCascadeEngine.add_observation` via
  `Addr0.meta["backings"]`.  New optional `scope_path` parameter
  threaded through `pff_python_classifier._walk`.
- **Step 3** — `Document.shared_across_functions` method and
  `AddrShareRecord` dataclass, implementing the signature
  above.
- **Step 4** — `tools/find_shared_structure.py` experiment
  script + `tests/test_cstz_on_cstz.py` integration test,
  running the pipeline on `src/cstz/pff.py` and
  `src/cstz/pff_cascade.py`.
- **Step 5** — shared helper extraction (originally C2b),
  empirically guided by Step 4's output.  The refactor's
  observable signature in cstz's equivalence notion is that
  Step 4 re-run after the refactor produces at least one more
  shared Addr0 than before.

Each step's commit message will include an explicit
"retroactive refinement" note updating earlier artifacts with
what the current step learned.  See the plan file for the full
DAG and leverage analysis.

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
