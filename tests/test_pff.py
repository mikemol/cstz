"""Tests for the PFF / RHPF data model in cstz.pff.

Step 1 of the PFF realignment plan: cover dataclasses, SHACL validators,
JSON serialization, and the alpha-rename merge protocol.

These tests do not require jsonschema; they exercise the Python
re-encoding of the SHACL constraints directly.
"""

from __future__ import annotations

import json

import pytest

from cstz.pff import (
    ADDR1_CTORS,
    ADDR2_CTORS,
    HOP_SIDES,
    IDENTIFIER_SCOPE,
    PAIR_ROLES,
    PFF_VERSION,
    SEVERITIES,
    SHADOW_EDGE_KINDS,
    SHADOW_NODE_KINDS,
    STEP_KINDS,
    WF_STATUSES,
    Addr0,
    Addr1,
    Addr2,
    Boundary,
    Chart,
    ClassMember,
    ClassView,
    Document,
    DocumentReceipt,
    Hop,
    Pair,
    Patch,
    PatchBundle,
    Port,
    Rank,
    Segment,
    Shadow,
    ShadowEdge,
    ShadowNode,
    Step,
    ValidationIssue,
)


# ── Helpers ─────────────────────────────────────────────────────────


def _minimal_doc(document_id: str = "d1") -> Document:
    """A minimal valid PFF document: one rank, one patch, one chart, one addr0."""
    return Document(
        documentId=document_id,
        ranks=[Rank(id="r0", ordinal=0, label="boot", note="bootstrap rank")],
        patches=[Patch(id="p0", rank="r0", phase="ingest")],
        charts=[Chart(id="c0", root="node:0", patch="p0")],
        addresses0=[Addr0(
            id="a0",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(
                    chart="c0", root="node:0",
                    route=[Step(kind="child", arg=0)],
                    role="principal",
                )],
            )],
        )],
    )


# ── Constants and enums ─────────────────────────────────────────────


def test_constants_match_schema():
    assert PFF_VERSION == "1.0"
    assert IDENTIFIER_SCOPE == "document-local"
    assert STEP_KINDS == ("child", "field", "pack", "share", "port")
    assert HOP_SIDES == ("left", "right", "both")
    assert PAIR_ROLES == ("principal", "aux")
    assert "glue" in ADDR1_CTORS
    assert "coh" in ADDR2_CTORS
    assert SHADOW_NODE_KINDS == ("semantic", "packed", "intermediate")
    assert SHADOW_EDGE_KINDS == ("contains", "premise", "projectsTo")
    assert WF_STATUSES == ("clean", "stored-with-violations", "rejected")
    assert SEVERITIES == ("info", "warning", "error", "fatal")


# ── Atomic dataclass to_json ────────────────────────────────────────


def test_rank_to_json_omits_optionals():
    assert Rank(id="r", ordinal=3).to_json() == {"id": "r", "ordinal": 3}
    assert Rank(id="r", ordinal=3, label="x", note="y").to_json() == {
        "id": "r", "ordinal": 3, "label": "x", "note": "y",
    }


def test_port_to_json():
    assert Port(name="lhs").to_json() == {"name": "lhs"}
    assert Port(name="lhs", role="input").to_json() == {"name": "lhs", "role": "input"}


def test_boundary_to_json_and_has_port():
    b = Boundary(id="B", ports=[Port(name="lhs"), Port(name="rhs", role="output")])
    js = b.to_json()
    assert js["id"] == "B"
    assert js["ports"] == [
        {"name": "lhs"},
        {"name": "rhs", "role": "output"},
    ]
    assert b.has_port("lhs")
    assert b.has_port("rhs")
    assert not b.has_port("missing")


def test_patch_to_json_with_all_fields():
    p = Patch(
        id="p", rank="r", phase="ingest",
        leftBoundary="bL", rightBoundary="bR",
        label="hello", meta={"a": 1},
    )
    js = p.to_json()
    assert js == {
        "id": "p", "rank": "r", "phase": "ingest",
        "leftBoundary": "bL", "rightBoundary": "bR",
        "label": "hello", "meta": {"a": 1},
    }


def test_patch_to_json_minimal():
    p = Patch(id="p", rank="r", phase="ingest")
    js = p.to_json()
    assert js == {"id": "p", "rank": "r", "phase": "ingest"}


def test_chart_to_json_payload_and_kind():
    c = Chart(id="c", root="n", patch="p", kind="sigma", payload={"k": "v"})
    js = c.to_json()
    assert js == {
        "id": "c", "root": "n", "patch": "p", "kind": "sigma",
        "payload": {"k": "v"},
    }
    minimal = Chart(id="c", root="n").to_json()
    assert minimal == {"id": "c", "root": "n"}


def test_step_to_json():
    assert Step(kind="child").to_json() == {"kind": "child"}
    assert Step(kind="child", arg=2).to_json() == {"kind": "child", "arg": 2}
    assert Step(kind="field", arg="lhs").to_json() == {"kind": "field", "arg": "lhs"}


def test_hop_to_json():
    h = Hop(boundary="B", side="left", port="lhs")
    assert h.to_json() == {"boundary": "B", "side": "left", "port": "lhs"}


def test_pair_to_json():
    p = Pair(
        chart="c", root="n",
        route=[Step(kind="child", arg=0), Step(kind="field", arg="x")],
        boundary=[Hop(boundary="B", side="right", port="rhs")],
        role="aux",
    )
    js = p.to_json()
    assert js["chart"] == "c"
    assert js["role"] == "aux"
    assert len(js["route"]) == 2
    assert len(js["boundary"]) == 1


def test_segment_to_json():
    s = Segment(rank="r", phase="ingest", patch="p", pairs=[
        Pair(chart="c", root="n", role="principal"),
    ])
    js = s.to_json()
    assert js["rank"] == "r"
    assert js["phase"] == "ingest"
    assert js["patch"] == "p"
    assert len(js["pairs"]) == 1


def test_addr0_to_json():
    a = Addr0(
        id="a", segments=[Segment(rank="r", phase="ingest", patch="p", pairs=[
            Pair(chart="c", root="n", role="principal"),
        ])],
        sort="Decl", discoveryRank="r",
        payload={"src": "x.py"}, meta={"line": 1},
    )
    js = a.to_json()
    assert js["sort"] == "Decl"
    assert js["discoveryRank"] == "r"
    assert js["payload"] == {"src": "x.py"}
    assert js["meta"] == {"line": 1}


def test_addr0_to_json_minimal():
    a = Addr0(id="a", segments=[Segment(
        rank="r", phase="ingest", patch="p",
        pairs=[Pair(chart="c", root="n", role="principal")],
    )])
    js = a.to_json()
    assert "sort" not in js
    assert "discoveryRank" not in js
    assert "payload" not in js
    assert "meta" not in js


def test_addr1_to_json_full_and_minimal():
    p = Addr1(
        id="g1", rank="r", ctor="glue", src="a", dst="b",
        patch="p", boundary="B",
        premises=["g0"], label="η-merge", args={"reason": "structural"},
    )
    js = p.to_json()
    assert js["ctor"] == "glue"
    assert js["premises"] == ["g0"]
    assert js["label"] == "η-merge"
    assert js["args"] == {"reason": "structural"}
    assert js["patch"] == "p"

    minimal = Addr1(id="g0", rank="r", ctor="refl", src="a", dst="a").to_json()
    assert "patch" not in minimal
    assert "boundary" not in minimal
    assert minimal["premises"] == []


def test_addr2_to_json_full_and_minimal():
    p = Addr2(
        id="c1", rank="r", ctor="coh", src="g1", dst="g2",
        patch="p", label="confluence", args={"k": 1},
    )
    js = p.to_json()
    assert js["ctor"] == "coh"
    assert js["label"] == "confluence"
    assert js["args"] == {"k": 1}
    assert js["patch"] == "p"

    minimal = Addr2(id="c2", rank="r", ctor="vcomp", src="g1", dst="g3").to_json()
    assert "label" not in minimal
    assert "args" not in minimal
    assert "patch" not in minimal


# ── Derived views ───────────────────────────────────────────────────


def test_classmember_to_json():
    m = ClassMember(classId="K1", address0="a0")
    assert m.to_json() == {"classId": "K1", "address0": "a0"}


def test_classview_full_and_minimal():
    cv = ClassView(
        id="cv1", rank="r0", phase="settled", truncation="full",
        congruence="alpha-eta",
        members=[ClassMember(classId="K1", address0="a0")],
        policy="https://example.org/policy",
    )
    js = cv.to_json()
    assert js["isAuthoritative"] is False
    assert js["congruence"] == "alpha-eta"
    assert js["policy"] == "https://example.org/policy"
    assert len(js["members"]) == 1

    minimal = ClassView(
        id="cv2", rank="r0", phase="settled", truncation="full",
        congruence="syntactic",
    ).to_json()
    assert "policy" not in minimal


def test_shadow_node_full_and_minimal():
    n = ShadowNode(id="n1", kind="semantic", label="Decl", backing=["a0", "a1"])
    js = n.to_json()
    assert js["label"] == "Decl"
    assert js["backing"] == ["a0", "a1"]

    minimal = ShadowNode(id="n2", kind="packed").to_json()
    assert "label" not in minimal
    assert minimal["backing"] == []


def test_shadow_edge_full_and_minimal():
    e = ShadowEdge(src="n1", dst="n2", kind="contains", ordinal=0)
    js = e.to_json()
    assert js["ordinal"] == 0

    minimal = ShadowEdge(src="n1", dst="n2", kind="premise").to_json()
    assert "ordinal" not in minimal


def test_shadow_full_and_minimal():
    sh = Shadow(
        id="sh1", rank="r0", phase="settled", truncation="full",
        congruence="alpha-eta",
        nodes=[ShadowNode(id="n1", kind="semantic")],
        edges=[ShadowEdge(src="n1", dst="n1", kind="contains")],
        policy="https://example.org/policy",
    )
    js = sh.to_json()
    assert js["isAuthoritative"] is False
    assert js["policy"] == "https://example.org/policy"
    assert len(js["nodes"]) == 1
    assert len(js["edges"]) == 1

    minimal = Shadow(
        id="sh2", rank="r0", phase="settled", truncation="full",
        congruence="syntactic",
    ).to_json()
    assert "policy" not in minimal


# ── ValidationIssue ─────────────────────────────────────────────────


def test_validation_issue_to_json():
    v = ValidationIssue(rule="WF-1", location="/x", severity="warning", message="m")
    assert v.to_json() == {
        "rule": "WF-1", "location": "/x", "severity": "warning", "message": "m",
    }


def test_validation_issue_rejects_unknown_severity():
    with pytest.raises(ValueError, match="unknown severity"):
        ValidationIssue(rule="r", location="l", severity="oops", message="m")


# ── DocumentReceipt ─────────────────────────────────────────────────


def test_receipt_clean_is_200():
    r = DocumentReceipt(
        documentId="d", accepted=True, wfStatus="clean", violations=[],
    )
    assert r.http_status == 200
    js = r.to_json()
    assert js == {
        "documentId": "d", "accepted": True, "wfStatus": "clean", "violations": [],
    }


def test_receipt_warnings_is_207():
    r = DocumentReceipt(
        documentId="d", accepted=True, wfStatus="stored-with-violations",
        violations=[ValidationIssue(rule="r", location="l", severity="warning", message="m")],
        rank="r0", warnings=["dangling reference"],
    )
    assert r.http_status == 207
    js = r.to_json()
    assert js["rank"] == "r0"
    assert js["warnings"] == ["dangling reference"]


def test_receipt_rejected_is_422():
    r = DocumentReceipt(
        documentId="d", accepted=False, wfStatus="rejected",
        violations=[ValidationIssue(rule="r", location="l", severity="fatal", message="m")],
    )
    assert r.http_status == 422


# ── Document validation ────────────────────────────────────────────


def test_minimal_doc_is_clean():
    d = _minimal_doc()
    receipt = d.receipt()
    assert receipt.wfStatus == "clean"
    assert receipt.accepted is True
    assert receipt.violations == []
    assert receipt.http_status == 200


def test_empty_doc_is_rejected():
    d = Document(documentId="empty")
    receipt = d.receipt()
    assert receipt.wfStatus == "rejected"
    assert receipt.accepted is False
    assert any(v.rule == "DocumentShape" for v in receipt.violations)


def test_unique_id_violation():
    d = _minimal_doc()
    d.patches.append(Patch(id="p0", rank="r0", phase="other"))  # duplicate id
    issues = d.validate()
    assert any(v.rule == "UniqueId" and "patches" in v.location for v in issues)


def test_dangling_rank_reference_in_patch():
    d = _minimal_doc()
    d.patches[0].rank = "missing"
    issues = d.validate()
    assert any(v.rule == "PatchShape.patchRank" for v in issues)


def test_dangling_rank_reference_in_paths():
    d = _minimal_doc()
    d.paths1.append(Addr1(id="g1", rank="missing", ctor="refl", src="a0", dst="a0"))
    d.paths2.append(Addr2(id="c1", rank="missing", ctor="coh", src="g1", dst="g1"))
    issues = d.validate()
    assert any(v.rule == "Addr1Shape.rank" for v in issues)
    assert any(v.rule == "Addr2Shape.rank" for v in issues)


def test_dangling_boundary_in_patch():
    d = _minimal_doc()
    d.patches[0].leftBoundary = "missing"
    d.patches[0].rightBoundary = "also-missing"
    issues = d.validate()
    assert any(v.rule == "PatchShape.leftBoundary" for v in issues)
    assert any(v.rule == "PatchShape.rightBoundary" for v in issues)


def test_chart_with_dangling_patch():
    d = _minimal_doc()
    d.charts.append(Chart(id="c1", root="n", patch="missing"))
    issues = d.validate()
    assert any(v.rule == "ChartShape.patch" for v in issues)


def test_chart_with_empty_root():
    d = _minimal_doc()
    d.charts.append(Chart(id="c1", root=""))
    issues = d.validate()
    assert any(v.rule == "ChartShape.chartRoot" for v in issues)


def test_addr0_without_segments_is_fatal():
    d = _minimal_doc()
    d.addresses0.append(Addr0(id="a1", segments=[]))
    issues = d.validate()
    assert any(
        v.rule == "Addr0Shape.hasSegment" and "/addresses0/1" in v.location
        for v in issues
    )


def test_addr0_duplicate_segment_rank_is_fatal():
    d = _minimal_doc()
    d.addresses0[0].segments.append(Segment(
        rank="r0", phase="ingest", patch="p0",
        pairs=[Pair(chart="c0", root="node:0", role="aux")],
    ))
    issues = d.validate()
    assert any(v.rule == "UniqueSegmentRankPerAddr0" for v in issues)


def test_addr0_segment_unknown_rank_is_fatal():
    d = _minimal_doc()
    d.addresses0[0].segments[0].rank = "ghost"
    issues = d.validate()
    assert any(v.rule == "SegmentShape.segmentRank" for v in issues)


def test_addr0_non_monotone_segments():
    d = _minimal_doc()
    d.ranks.append(Rank(id="r1", ordinal=1))
    d.ranks.append(Rank(id="r2", ordinal=2))
    d.addresses0[0].segments = [
        Segment(rank="r2", phase="ingest", patch="p0",
                pairs=[Pair(chart="c0", root="node:0", role="principal")]),
        Segment(rank="r1", phase="ingest", patch="p0",
                pairs=[Pair(chart="c0", root="node:0", role="principal")]),
    ]
    issues = d.validate()
    assert any(v.rule == "MonotoneSegmentChain" for v in issues)


def test_segment_unknown_patch():
    d = _minimal_doc()
    d.addresses0[0].segments[0].patch = "ghost"
    issues = d.validate()
    assert any(v.rule == "SegmentShape.segmentPatch" for v in issues)


def test_segment_without_pairs():
    d = _minimal_doc()
    d.addresses0[0].segments[0].pairs = []
    issues = d.validate()
    assert any(v.rule == "SegmentShape.hasPair" for v in issues)


def test_pair_unknown_chart():
    d = _minimal_doc()
    d.addresses0[0].segments[0].pairs[0].chart = "ghost"
    issues = d.validate()
    assert any(v.rule == "PairShape.pairChart" for v in issues)


def test_pair_invalid_role():
    d = _minimal_doc()
    d.addresses0[0].segments[0].pairs[0].role = "bogus"
    issues = d.validate()
    assert any(v.rule == "PairShape.pairRole" for v in issues)


def test_pair_invalid_step_kind():
    d = _minimal_doc()
    d.addresses0[0].segments[0].pairs[0].route = [Step(kind="invalid")]
    issues = d.validate()
    assert any(v.rule == "StepShape.stepKind" for v in issues)


def test_pair_hop_unknown_boundary():
    d = _minimal_doc()
    d.addresses0[0].segments[0].pairs[0].boundary = [
        Hop(boundary="ghost", side="left", port="lhs"),
    ]
    issues = d.validate()
    assert any(v.rule == "HopShape.hopBoundary" for v in issues)


def test_pair_hop_invalid_side():
    d = _minimal_doc()
    d.boundaries.append(Boundary(id="B", ports=[Port(name="lhs")]))
    d.addresses0[0].segments[0].pairs[0].boundary = [
        Hop(boundary="B", side="bogus", port="lhs"),
    ]
    issues = d.validate()
    assert any(v.rule == "HopShape.hopSide" for v in issues)


def test_pair_hop_port_not_on_boundary():
    d = _minimal_doc()
    d.boundaries.append(Boundary(id="B", ports=[Port(name="lhs")]))
    d.addresses0[0].segments[0].pairs[0].boundary = [
        Hop(boundary="B", side="left", port="missing"),
    ]
    issues = d.validate()
    assert any(v.rule == "BoundaryPortCompatibility" for v in issues)


def test_pair_hop_port_compatible():
    d = _minimal_doc()
    d.boundaries.append(Boundary(id="B", ports=[Port(name="lhs")]))
    d.patches[0].leftBoundary = "B"
    d.addresses0[0].segments[0].pairs[0].boundary = [
        Hop(boundary="B", side="left", port="lhs"),
    ]
    receipt = d.receipt()
    assert receipt.wfStatus == "clean"


def test_path1_invalid_ctor_and_endpoints():
    d = _minimal_doc()
    d.paths1.append(Addr1(id="g1", rank="r0", ctor="invalid", src="ghost", dst="other"))
    issues = d.validate()
    assert any(v.rule == "Addr1Shape.ctor" for v in issues)
    assert any(v.rule == "Addr1Shape.src" for v in issues)
    assert any(v.rule == "Addr1Shape.dst" for v in issues)


def test_path2_invalid_ctor_and_endpoints():
    d = _minimal_doc()
    d.paths2.append(Addr2(id="c1", rank="r0", ctor="invalid", src="ghost", dst="other"))
    issues = d.validate()
    assert any(v.rule == "Addr2Shape.ctor" for v in issues)
    assert any(v.rule == "Addr2Shape.src" for v in issues)
    assert any(v.rule == "Addr2Shape.dst" for v in issues)


def test_path1_path2_well_formed():
    d = _minimal_doc()
    d.paths1.append(Addr1(id="g0", rank="r0", ctor="refl", src="a0", dst="a0"))
    d.paths1.append(Addr1(id="g1", rank="r0", ctor="glue", src="a0", dst="a0"))
    d.paths2.append(Addr2(id="c1", rank="r0", ctor="coh", src="g0", dst="g1"))
    receipt = d.receipt()
    assert receipt.wfStatus == "clean"


def test_classview_must_be_non_authoritative():
    d = _minimal_doc()
    d.classViews.append(ClassView(
        id="cv", rank="r0", phase="settled", truncation="full",
        congruence="syntactic", isAuthoritative=True,
    ))
    issues = d.validate()
    assert any(v.rule == "ClassViewShape.isAuthoritative" for v in issues)


def test_shadow_must_be_non_authoritative():
    d = _minimal_doc()
    d.shadows.append(Shadow(
        id="sh", rank="r0", phase="settled", truncation="full",
        congruence="syntactic", isAuthoritative=True,
    ))
    issues = d.validate()
    assert any(v.rule == "ShadowShape.isAuthoritative" for v in issues)


def test_non_authoritative_views_pass_validation():
    """Exercises the false branch of the isAuthoritative loops."""
    d = _minimal_doc()
    d.classViews.append(ClassView(
        id="cv", rank="r0", phase="settled", truncation="full",
        congruence="syntactic",  # isAuthoritative defaults to False
    ))
    d.shadows.append(Shadow(
        id="sh", rank="r0", phase="settled", truncation="full",
        congruence="syntactic",
    ))
    receipt = d.receipt()
    assert receipt.wfStatus == "clean"


def test_receipt_stored_with_violations_for_non_fatal_issues():
    """Non-fatal violations (severity=error) yield 207, accepted=True."""
    d = _minimal_doc()
    # Dangling boundary in patch is severity=error, not fatal
    d.patches[0].leftBoundary = "ghost"
    receipt = d.receipt()
    assert receipt.wfStatus == "stored-with-violations"
    assert receipt.accepted is True
    assert receipt.http_status == 207
    assert any(v.severity == "error" for v in receipt.violations)


# ── Document lookup helpers ─────────────────────────────────────────


def test_lookup_helpers():
    d = _minimal_doc()
    d.boundaries.append(Boundary(id="B", ports=[Port(name="lhs")]))
    assert d.rank_by_id("r0") is not None
    assert d.rank_by_id("ghost") is None
    assert d.patch_by_id("p0") is not None
    assert d.patch_by_id("ghost") is None
    assert d.chart_by_id("c0") is not None
    assert d.chart_by_id("ghost") is None
    assert d.boundary_by_id("B") is not None
    assert d.boundary_by_id("ghost") is None
    assert d.addr0_by_id("a0") is not None
    assert d.addr0_by_id("ghost") is None


# ── JSON serialization ─────────────────────────────────────────────


def test_to_pff_json_minimal():
    d = _minimal_doc()
    js = d.to_pff_json()
    assert js["version"] == "1.0"
    assert js["identifierScope"] == "document-local"
    assert js["documentId"] == "d1"
    # Required collections present
    for key in ("ranks", "patches", "charts", "addresses0",
                "boundaries", "paths1", "paths2", "classViews", "shadows"):
        assert key in js
    # JSON-serializable
    blob = json.dumps(js)
    assert "node:0" in blob


def test_to_pff_json_includes_baseiri_and_namespaces():
    d = _minimal_doc()
    d.baseIri = "https://example.org/d/"
    d.namespaces = {"ex": "https://example.org/"}
    js = d.to_pff_json()
    assert js["baseIri"] == "https://example.org/d/"
    assert js["namespaces"] == {"ex": "https://example.org/"}


def test_to_pff_json_omits_baseiri_and_namespaces_when_absent():
    d = _minimal_doc()
    js = d.to_pff_json()
    assert "baseIri" not in js
    assert "namespaces" not in js


# ── PatchBundle ────────────────────────────────────────────────────


def test_patch_bundle_to_json_shape():
    bundle = PatchBundle(
        ranks=[Rank(id="r0", ordinal=0)],
        patches=[Patch(id="p0", rank="r0", phase="ingest")],
    )
    js = bundle.to_json()
    assert js["version"] == "1.0"
    assert js["identifierScope"] == "document-local"
    assert len(js["patches"]) == 1
    assert len(js["ranks"]) == 1


# ── Merge / alpha-rename ───────────────────────────────────────────


def test_merge_no_collision_appends_records():
    d = _minimal_doc()
    bundle = PatchBundle(
        ranks=[Rank(id="r1", ordinal=1)],
        patches=[Patch(id="p1", rank="r1", phase="derive")],
    )
    receipt = d.merge_bundle(bundle)
    assert receipt.wfStatus == "clean"
    assert any(r.id == "r1" for r in d.ranks)
    assert any(p.id == "p1" and p.rank == "r1" for p in d.patches)


def test_merge_renames_colliding_ids_and_rewrites_references():
    d = _minimal_doc()
    bundle = PatchBundle(
        ranks=[Rank(id="r0", ordinal=1, label="from-bundle")],
        patches=[Patch(id="p0", rank="r0", phase="derive")],
    )
    receipt = d.merge_bundle(bundle)
    # The bundle's r0 became r0~1, and the bundle's p0 still references it
    rank_ids = [r.id for r in d.ranks]
    assert "r0~1" in rank_ids
    renamed_patch = next(p for p in d.patches if p.id == "p0~1")
    assert renamed_patch.rank == "r0~1"
    assert receipt.wfStatus == "clean"


def test_merge_repeated_collisions_pick_distinct_suffixes():
    d = _minimal_doc()
    # Pre-populate a r0~1 so the next collision must pick r0~2
    d.ranks.append(Rank(id="r0~1", ordinal=1))
    bundle = PatchBundle(ranks=[Rank(id="r0", ordinal=2)])
    d.merge_bundle(bundle)
    rank_ids = [r.id for r in d.ranks]
    assert "r0~2" in rank_ids


def test_merge_full_bundle_preserves_internal_references():
    """Bundle with colliding ids on every kind; verify cross-refs are rewritten."""
    d = _minimal_doc()
    # Pre-populate B0 in the host so the bundle's B0 must be renamed too
    d.boundaries.append(Boundary(id="B0", ports=[Port(name="lhs")]))
    d.patches[0].leftBoundary = "B0"

    bundle = PatchBundle(
        ranks=[Rank(id="r0", ordinal=1)],
        boundaries=[Boundary(id="B0", ports=[Port(name="lhs"), Port(name="rhs")])],
        patches=[Patch(
            id="p0", rank="r0", phase="derive",
            leftBoundary="B0", rightBoundary="B0",
            label="bundled", meta={"src": "test"},
        )],
        charts=[Chart(id="c0", root="bundle:0", patch="p0", kind="sigma",
                      payload={"k": 1})],
        addresses0=[Addr0(
            id="a0",
            segments=[Segment(
                rank="r0", phase="derive", patch="p0",
                pairs=[Pair(
                    chart="c0", root="bundle:0",
                    route=[Step(kind="child", arg=0)],
                    boundary=[Hop(boundary="B0", side="left", port="lhs")],
                    role="aux",
                )],
            )],
            sort="Decl", discoveryRank="r0",
            payload={"x": 1}, meta={"y": 2},
        )],
        paths1=[Addr1(
            id="g0", rank="r0", ctor="glue", src="a0", dst="a0",
            patch="p0", boundary="B0",
            premises=["a0"], label="glue-step", args={"why": "test"},
        )],
        paths2=[Addr2(
            id="k0", rank="r0", ctor="coh", src="g0", dst="g0",
            patch="p0", label="coh-step", args={"why": "test"},
        )],
    )
    receipt = d.merge_bundle(bundle)
    assert receipt.wfStatus == "clean"

    # The bundle's "0"-suffixed records should all have been renamed to ~1
    renamed_addr0 = next(a for a in d.addresses0 if a.id == "a0~1")
    seg = renamed_addr0.segments[0]
    assert seg.rank == "r0~1"
    assert seg.patch == "p0~1"
    assert seg.phase == "derive"
    pair = seg.pairs[0]
    assert pair.chart == "c0~1"
    assert pair.role == "aux"
    # B0 collided too, so the hop's boundary was rewritten
    assert pair.boundary[0].boundary == "B0~1"
    assert pair.boundary[0].port == "lhs"
    assert renamed_addr0.discoveryRank == "r0~1"
    assert renamed_addr0.payload == {"x": 1}
    assert renamed_addr0.meta == {"y": 2}

    # Patch references on the renamed patch should all carry the renamed boundary
    renamed_patch = next(p for p in d.patches if p.id == "p0~1")
    assert renamed_patch.leftBoundary == "B0~1"
    assert renamed_patch.rightBoundary == "B0~1"
    assert renamed_patch.meta == {"src": "test"}
    assert renamed_patch.label == "bundled"

    # Chart payload preserved, patch ref rewritten
    renamed_chart = next(c for c in d.charts if c.id == "c0~1")
    assert renamed_chart.patch == "p0~1"
    assert renamed_chart.kind == "sigma"
    assert renamed_chart.payload == {"k": 1}

    # paths1: id g0 didn't collide (the host has none), but its rank, addr0,
    # patch, and boundary refs all did → must be rewritten.
    g = next(p for p in d.paths1 if p.id == "g0")
    assert g.ctor == "glue"
    assert g.rank == "r0~1"
    assert g.src == "a0~1"
    assert g.dst == "a0~1"
    assert g.patch == "p0~1"
    assert g.boundary == "B0~1"
    assert g.premises == ["a0~1"]
    assert g.label == "glue-step"
    assert g.args == {"why": "test"}

    # paths2 likewise
    k = next(p for p in d.paths2 if p.id == "k0")
    assert k.ctor == "coh"
    assert k.rank == "r0~1"
    assert k.src == "g0"  # didn't collide
    assert k.dst == "g0"
    assert k.patch == "p0~1"
    assert k.args == {"why": "test"}


def test_merge_into_empty_doc():
    d = Document(documentId="d-empty")
    bundle = PatchBundle(
        ranks=[Rank(id="r0", ordinal=0)],
        patches=[Patch(id="p0", rank="r0", phase="ingest")],
        charts=[Chart(id="c0", root="n0", patch="p0")],
        addresses0=[Addr0(id="a0", segments=[Segment(
            rank="r0", phase="ingest", patch="p0",
            pairs=[Pair(chart="c0", root="n0", role="principal")],
        )])],
    )
    receipt = d.merge_bundle(bundle)
    assert receipt.wfStatus == "clean"
    assert len(d.ranks) == 1
    assert len(d.patches) == 1


# ── all_identifiers iterator ────────────────────────────────────────


def test_all_identifiers_yields_every_id_kind():
    d = _minimal_doc()
    d.boundaries.append(Boundary(id="B", ports=[Port(name="lhs")]))
    d.paths1.append(Addr1(id="g0", rank="r0", ctor="refl", src="a0", dst="a0"))
    d.paths2.append(Addr2(id="k0", rank="r0", ctor="coh", src="g0", dst="g0"))
    d.classViews.append(ClassView(
        id="cv", rank="r0", phase="settled", truncation="full",
        congruence="syntactic",
    ))
    d.shadows.append(Shadow(
        id="sh", rank="r0", phase="settled", truncation="full",
        congruence="syntactic",
    ))
    ids = list(d.all_identifiers())
    for needle in ("r0", "p0", "c0", "a0", "B", "g0", "k0", "cv", "sh"):
        assert needle in ids
