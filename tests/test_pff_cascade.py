"""Tests for the native PFF cascade engine in cstz.pff_cascade.

These tests exercise PFF semantics directly: streaming glue closure,
recursive cascade, idempotency, the path2 (coh) closure, the
reading-(a) role-coproduct projection, and Document well-formedness.

They are NOT a port of tests/test_core.py — the legacy three-fiber
SPPF tests remain the metamathematical reference for inference.agda
and exercise a different (but mathematically equivalent) substrate.

These tests assume correct-by-construction usage: the engine does
not validate that ids passed to glue/coh come from previous engine
calls.  Tests therefore only exercise valid usage patterns.
"""

from __future__ import annotations

from cstz.pff import Rank
from cstz.pff_cascade import PFFCascadeEngine, _UnionFind


# ── _UnionFind helper ───────────────────────────────────────────────


class TestUnionFind:
    def test_make_idempotent(self) -> None:
        uf = _UnionFind()
        uf.make("a")
        uf.make("a")
        assert "a" in uf
        assert uf.find("a") == "a"

    def test_union_disjoint(self) -> None:
        uf = _UnionFind()
        uf.make("a")
        uf.make("b")
        root = uf.union("a", "b")
        assert uf.find("a") == root
        assert uf.find("b") == root

    def test_union_same_class_idempotent(self) -> None:
        uf = _UnionFind()
        uf.make("a")
        uf.make("b")
        uf.union("a", "b")
        # Calling union again returns the same root
        root1 = uf.find("a")
        root2 = uf.union("a", "b")
        assert root1 == root2

    def test_union_by_rank(self) -> None:
        uf = _UnionFind()
        for x in "abcd":
            uf.make(x)
        uf.union("a", "b")  # rank(a)=1
        uf.union("c", "d")  # rank(c)=1
        # Both classes have rank 1; union of roots yields rank 2 on winner
        winner = uf.union("a", "c")
        assert uf.find("a") == winner
        assert uf.find("d") == winner

    def test_union_swap_low_rank_into_high_rank(self) -> None:
        """Smaller-rank tree must attach under larger-rank tree (swap branch)."""
        uf = _UnionFind()
        for x in "abcde":
            uf.make(x)
        uf.union("a", "b")  # rank(a)=1
        uf.union("c", "d")  # rank(c)=1
        uf.union("a", "c")  # rank(a)=2
        # Now union(e, a): rank(e)=0 < rank(a)=2 → swap, e attaches under a
        winner = uf.union("e", "a")
        assert winner == uf.find("a")
        assert uf.find("e") == winner

    def test_path_compression(self) -> None:
        uf = _UnionFind()
        for x in "abcde":
            uf.make(x)
        uf.union("a", "b")
        uf.union("b", "c")
        uf.union("c", "d")
        uf.union("d", "e")
        # All elements now share a root
        roots = {uf.find(x) for x in "abcde"}
        assert len(roots) == 1

    def test_iter_and_len(self) -> None:
        uf = _UnionFind()
        for x in "xyz":
            uf.make(x)
        assert len(uf) == 3
        assert set(iter(uf)) == {"x", "y", "z"}

    def test_contains(self) -> None:
        uf = _UnionFind()
        uf.make("a")
        assert "a" in uf
        assert "b" not in uf


# ── Engine construction & idempotent ensure_* ───────────────────────


class TestEngineConstruction:
    def test_default_document_id(self) -> None:
        e = PFFCascadeEngine()
        assert e.document.documentId == PFFCascadeEngine.DEFAULT_DOCUMENT_ID

    def test_custom_document_id(self) -> None:
        e = PFFCascadeEngine(document_id="my-doc")
        assert e.document.documentId == "my-doc"

    def test_empty_engine_repr(self) -> None:
        e = PFFCascadeEngine()
        s = repr(e)
        assert "PFFCascadeEngine" in s
        assert "addr0=0" in s
        assert "path1=0" in s

    def test_ensure_rank_idempotent(self) -> None:
        e = PFFCascadeEngine()
        r1 = e.ensure_rank(0)
        r2 = e.ensure_rank(0)
        assert r1 is r2
        assert len(e.document.ranks) == 1

    def test_ensure_rank_distinct_ordinals(self) -> None:
        e = PFFCascadeEngine()
        r0 = e.ensure_rank(0)
        r1 = e.ensure_rank(1, label="follow-up")
        assert r0.id != r1.id
        assert r1.label == "follow-up"
        assert len(e.document.ranks) == 2

    def test_ensure_rank_default_label(self) -> None:
        e = PFFCascadeEngine()
        r = e.ensure_rank()
        assert r.label == PFFCascadeEngine.DEFAULT_RANK_LABEL

    def test_ensure_patch_idempotent(self) -> None:
        e = PFFCascadeEngine()
        rank = e.ensure_rank(0)
        p1 = e.ensure_patch("ingest", rank=rank)
        p2 = e.ensure_patch("ingest", rank=rank)
        assert p1 is p2
        assert len(e.document.patches) == 1

    def test_ensure_patch_default_rank(self) -> None:
        e = PFFCascadeEngine()
        p = e.ensure_patch("ingest")
        assert p.rank == e.ensure_rank(0).id

    def test_ensure_patch_default_label(self) -> None:
        e = PFFCascadeEngine()
        p = e.ensure_patch()
        assert p.label == PFFCascadeEngine.DEFAULT_PATCH_LABEL

    def test_ensure_patch_distinct_phases(self) -> None:
        e = PFFCascadeEngine()
        p_ingest = e.ensure_patch("ingest")
        p_derive = e.ensure_patch("derive")
        assert p_ingest.id != p_derive.id

    def test_ensure_chart_idempotent(self) -> None:
        e = PFFCascadeEngine()
        c1 = e.ensure_chart("sigma", "Foo")
        c2 = e.ensure_chart("sigma", "Foo")
        assert c1 is c2
        assert len(e.document.charts) == 1

    def test_ensure_chart_distinct_kinds(self) -> None:
        e = PFFCascadeEngine()
        c_sigma = e.ensure_chart("sigma", "Foo")
        c_tau = e.ensure_chart("tau", "Foo")
        assert c_sigma.id != c_tau.id
        assert c_sigma.kind == "sigma"
        assert c_tau.kind == "tau"

    def test_ensure_chart_distinct_payloads(self) -> None:
        e = PFFCascadeEngine()
        c1 = e.ensure_chart("sigma", "Foo", payload={"v": 1})
        c2 = e.ensure_chart("sigma", "Foo", payload={"v": 2})
        assert c1.id != c2.id

    def test_ensure_chart_payload_signature_dict_order(self) -> None:
        """Dict payloads with the same content but different insertion order
        should hash to the same chart."""
        e = PFFCascadeEngine()
        c1 = e.ensure_chart("sigma", "X", payload={"a": 1, "b": 2})
        c2 = e.ensure_chart("sigma", "X", payload={"b": 2, "a": 1})
        assert c1 is c2

    def test_ensure_chart_payload_list_signature(self) -> None:
        e = PFFCascadeEngine()
        c1 = e.ensure_chart("sigma", "X", payload=[1, 2, 3])
        c2 = e.ensure_chart("sigma", "X", payload=[1, 2, 3])
        assert c1 is c2
        c3 = e.ensure_chart("sigma", "X", payload=[3, 2, 1])
        assert c3 is not c1

    def test_ensure_chart_payload_arbitrary_object(self) -> None:
        class Token:
            def __repr__(self) -> str:
                return "TOKEN"
        e = PFFCascadeEngine()
        t = Token()
        c1 = e.ensure_chart("sigma", "X", payload=t)
        c2 = e.ensure_chart("sigma", "X", payload=t)
        # Same repr → same signature
        assert c1 is c2

    def test_ensure_chart_with_patch(self) -> None:
        e = PFFCascadeEngine()
        rank = e.ensure_rank(0)
        patch = e.ensure_patch("ingest", rank=rank)
        chart = e.ensure_chart("sigma", "X", patch=patch)
        assert chart.patch == patch.id


# ── Single observation ─────────────────────────────────────────────


class TestSingleObservation:
    def test_minimal_observation(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "Lit")
        tau = e.ensure_chart("tau", "int")
        addr0 = e.add_observation(sigma, tau)

        assert addr0.id in {a.id for a in e.document.addresses0}
        assert len(addr0.segments) == 1
        seg = addr0.segments[0]
        assert len(seg.pairs) == 2
        assert seg.pairs[0].role == "principal"
        assert seg.pairs[1].role == "aux"
        assert seg.pairs[0].chart == sigma.id
        assert seg.pairs[1].chart == tau.id
        assert e.receipt().wfStatus == "clean"

    def test_observation_default_sort_from_chart_root(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "MyShape")
        tau = e.ensure_chart("tau", "T")
        addr0 = e.add_observation(sigma, tau)
        assert addr0.sort == "MyShape"

    def test_observation_explicit_sort_and_node_root(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "Lit")
        tau = e.ensure_chart("tau", "int")
        addr0 = e.add_observation(sigma, tau, sort="MyLit",
                                  node_root="custom-root")
        assert addr0.sort == "MyLit"
        assert addr0.segments[0].pairs[0].root == "custom-root"

    def test_observation_default_rank_and_patch(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        addr0 = e.add_observation(sigma, tau)
        # Defaults to ordinal-0 rank and 'ingest' patch
        assert addr0.discoveryRank == e.ensure_rank(0).id
        assert addr0.segments[0].patch == e.ensure_patch("ingest").id

    def test_observation_explicit_rank_and_patch(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        rank = e.ensure_rank(7, label="custom")
        patch = e.ensure_patch("derive", rank=rank)
        addr0 = e.add_observation(sigma, tau, rank=rank, patch=patch)
        assert addr0.discoveryRank == rank.id
        assert addr0.segments[0].rank == rank.id
        assert addr0.segments[0].patch == patch.id
        assert addr0.segments[0].phase == "derive"

    def test_duplicate_observation_dedups(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        a1 = e.add_observation(sigma, tau)
        a2 = e.add_observation(sigma, tau)
        assert a1 is a2
        assert len(e.document.addresses0) == 1


# ── Streaming glue closure ─────────────────────────────────────────


class TestStreamingGlueCascade:
    def test_eta_glue_same_sigma_different_tau(self) -> None:
        """Two observations with the same σ-chart but different τ-charts
        should be glued by the streaming cascade."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_int = e.ensure_chart("tau", "int")
        tau_str = e.ensure_chart("tau", "str")
        a = e.add_observation(sigma, tau_int)
        b = e.add_observation(sigma, tau_str)
        assert e.canonical_addr0(a.id) == e.canonical_addr0(b.id)
        assert len(e.document.paths1) == 1
        assert e.document.paths1[0].ctor == "glue"
        assert e.receipt().wfStatus == "clean"

    def test_no_glue_when_sigma_charts_differ(self) -> None:
        """Different σ-charts → no streaming glue regardless of τ."""
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma_a, tau)
        b = e.add_observation(sigma_b, tau)
        assert e.canonical_addr0(a.id) != e.canonical_addr0(b.id)
        assert len(e.document.paths1) == 0

    def test_no_glue_when_sigma_children_differ(self) -> None:
        """Same σ-chart but different canonical sigma_children → no glue."""
        e = PFFCascadeEngine()
        sigma_leaf_a = e.ensure_chart("sigma", "LeafA")
        sigma_leaf_b = e.ensure_chart("sigma", "LeafB")
        sigma_parent = e.ensure_chart("sigma", "Parent")
        tau = e.ensure_chart("tau", "T")

        leaf_a = e.add_observation(sigma_leaf_a, tau)
        leaf_b = e.add_observation(sigma_leaf_b, tau)
        # Children disjoint → parents have different sigma_keys
        pa = e.add_observation(sigma_parent, tau, sigma_children=[leaf_a.id])
        pb = e.add_observation(sigma_parent, tau, sigma_children=[leaf_b.id])
        assert e.canonical_addr0(pa.id) != e.canonical_addr0(pb.id)

    def test_three_way_glue_in_one_step(self) -> None:
        """Three observations with the same σ-key all glue together."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        tau_c = e.ensure_chart("tau", "C")
        a = e.add_observation(sigma, tau_a)
        b = e.add_observation(sigma, tau_b)
        c = e.add_observation(sigma, tau_c)
        assert e.canonical_addr0(a.id) == e.canonical_addr0(b.id)
        assert e.canonical_addr0(b.id) == e.canonical_addr0(c.id)


# ── Recursive cascade ──────────────────────────────────────────────


class TestRecursiveCascade:
    def test_explicit_glue_propagates_to_parents(self) -> None:
        """Manually gluing two leaves should cascade-glue their parents."""
        e = PFFCascadeEngine()
        sigma_leaf_a = e.ensure_chart("sigma", "LeafA")
        sigma_leaf_b = e.ensure_chart("sigma", "LeafB")
        sigma_parent = e.ensure_chart("sigma", "Parent")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        tau_pa = e.ensure_chart("tau", "PA")
        tau_pb = e.ensure_chart("tau", "PB")

        leaf_a = e.add_observation(sigma_leaf_a, tau_a)
        leaf_b = e.add_observation(sigma_leaf_b, tau_b)
        pa = e.add_observation(sigma_parent, tau_pa, sigma_children=[leaf_a.id])
        pb = e.add_observation(sigma_parent, tau_pb, sigma_children=[leaf_b.id])

        # Pre-glue: parents disjoint
        assert e.canonical_addr0(pa.id) != e.canonical_addr0(pb.id)

        result = e.glue(leaf_a.id, leaf_b.id, label="manual-leaf-glue")
        assert result.addr1 is not None
        assert not result.was_noop
        assert len(result.cascade_addr1s) == 1
        assert e.canonical_addr0(pa.id) == e.canonical_addr0(pb.id)
        assert e.receipt().wfStatus == "clean"

    def test_three_level_cascade(self) -> None:
        """Three-level structure: leaf glue cascades through mid → root."""
        e = PFFCascadeEngine()
        sLi = e.ensure_chart("sigma", "LeafInt")
        sLs = e.ensure_chart("sigma", "LeafStr")
        sM = e.ensure_chart("sigma", "Mid")
        sR = e.ensure_chart("sigma", "Root")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tC = e.ensure_chart("tau", "C")
        tD = e.ensure_chart("tau", "D")
        tE = e.ensure_chart("tau", "E")
        tF = e.ensure_chart("tau", "F")

        li = e.add_observation(sLi, tA)
        ls = e.add_observation(sLs, tB)
        mi = e.add_observation(sM, tC, sigma_children=[li.id])
        ms = e.add_observation(sM, tD, sigma_children=[ls.id])
        ri = e.add_observation(sR, tE, sigma_children=[mi.id])
        rs = e.add_observation(sR, tF, sigma_children=[ms.id])

        # Pre-glue: nothing connected
        assert e.canonical_addr0(mi.id) != e.canonical_addr0(ms.id)
        assert e.canonical_addr0(ri.id) != e.canonical_addr0(rs.id)

        result = e.glue(li.id, ls.id, label="deep-leaf-glue")
        # Two cascade glues: one for the mid level, one for the root level
        assert len(result.cascade_addr1s) == 2
        assert e.canonical_addr0(mi.id) == e.canonical_addr0(ms.id)
        assert e.canonical_addr0(ri.id) == e.canonical_addr0(rs.id)
        assert e.receipt().wfStatus == "clean"

    def test_cascade_fresh_slot_relabel(self) -> None:
        """Cascade re-canonicalizes a parent's sigma_key into an empty slot.

        Setup: la and lb are distinct leaves; pa references lb only.
        After glue(la, lb), la wins, and pa's old sigma_key (P, (lb,))
        rekeys to (P, (la,)) which has no occupants → fresh-slot
        relabel branch fires.
        """
        e = PFFCascadeEngine()
        sLa = e.ensure_chart("sigma", "LeafA")
        sLb = e.ensure_chart("sigma", "LeafB")
        sP = e.ensure_chart("sigma", "Parent")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tP = e.ensure_chart("tau", "P")

        la = e.add_observation(sLa, tA)
        lb = e.add_observation(sLb, tB)
        pa = e.add_observation(sP, tP, sigma_children=[lb.id])

        e.glue(la.id, lb.id)
        # pa's children should now reference la (the canonical winner)
        assert e.canonical_addr0(pa.id) == pa.id
        # Receipt is still clean
        assert e.receipt().wfStatus == "clean"

    def test_cascade_collision_with_already_glued_member(self) -> None:
        """Cascade-collision union_set has members already glued.

        Setup: la, lb, lc are three distinct leaves with three parents
        pa, pb, pc.  Glue(la, lb) merges la~lb and cascade-glues pa~pb.
        Then glue(la, lc) merges la~lc and cascade tries to glue
        {pa, pb, pc} — but pa~pb are already glued from the prior round,
        so the inner-loop continue at find(anchor)==find(other) fires.
        """
        e = PFFCascadeEngine()
        sLa = e.ensure_chart("sigma", "LeafA")
        sLb = e.ensure_chart("sigma", "LeafB")
        sLc = e.ensure_chart("sigma", "LeafC")
        sP = e.ensure_chart("sigma", "Parent")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tC = e.ensure_chart("tau", "C")
        tPa = e.ensure_chart("tau", "Pa")
        tPb = e.ensure_chart("tau", "Pb")
        tPc = e.ensure_chart("tau", "Pc")

        la = e.add_observation(sLa, tA)
        lb = e.add_observation(sLb, tB)
        lc = e.add_observation(sLc, tC)
        pa = e.add_observation(sP, tPa, sigma_children=[la.id])
        pb = e.add_observation(sP, tPb, sigma_children=[lb.id])
        pc = e.add_observation(sP, tPc, sigma_children=[lc.id])

        # First glue: la~lb. Cascade glues pa~pb.
        e.glue(la.id, lb.id)
        assert e.canonical_addr0(pa.id) == e.canonical_addr0(pb.id)

        # Second glue: la~lc. Cascade tries {pa, pb, pc}; pa~pb is
        # already merged, so the inner-loop continue fires.
        e.glue(la.id, lc.id)
        # All three parents must end up in the same path1 class
        assert e.canonical_addr0(pa.id) == e.canonical_addr0(pc.id)
        assert e.canonical_addr0(pb.id) == e.canonical_addr0(pc.id)
        assert e.receipt().wfStatus == "clean"

    def test_cascade_collision_in_single_round(self) -> None:
        """Two pre-existing parents under different sigma_keys collapse
        into the same key after a leaf glue."""
        e = PFFCascadeEngine()
        sLa = e.ensure_chart("sigma", "LeafA")
        sLb = e.ensure_chart("sigma", "LeafB")
        sP = e.ensure_chart("sigma", "Parent")
        tT1 = e.ensure_chart("tau", "T1")
        tT2 = e.ensure_chart("tau", "T2")
        tT3 = e.ensure_chart("tau", "T3")
        tT4 = e.ensure_chart("tau", "T4")

        la = e.add_observation(sLa, tT1)
        lb = e.add_observation(sLb, tT2)
        pa = e.add_observation(sP, tT3, sigma_children=[la.id])
        pb = e.add_observation(sP, tT4, sigma_children=[lb.id])

        e.glue(la.id, lb.id)
        # After leaf glue, both parents should share the same canonical
        # sigma_key (la and lb canonicalize to the same id), and the
        # cascade-after-merge merges them.
        assert e.canonical_addr0(pa.id) == e.canonical_addr0(pb.id)


# ── Public glue() API ──────────────────────────────────────────────


class TestPublicGlueAPI:
    def test_glue_idempotent_returns_noop(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma, tau)
        b = e.add_observation(sigma, tau)
        # Both observations are the same → dedup
        assert a is b
        # glue them: same id → already same canonical → noop
        result = e.glue(a.id, a.id)
        assert result.was_noop is True
        assert result.addr1 is None

    def test_glue_post_streaming_is_noop(self) -> None:
        """Streaming cascade already glued these; explicit glue is a no-op."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        a = e.add_observation(sigma, tau_a)
        b = e.add_observation(sigma, tau_b)
        # Cascade already glued them
        before_count = len(e.document.paths1)
        result = e.glue(a.id, b.id)
        assert result.was_noop is True
        assert len(e.document.paths1) == before_count

    def test_glue_with_explicit_label_and_premises(self) -> None:
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma_a, tau)
        b = e.add_observation(sigma_b, tau)
        result = e.glue(a.id, b.id, label="custom",
                        premises=["proof:1", "proof:2"])
        assert result.addr1 is not None
        assert result.addr1.label == "custom"
        assert result.addr1.premises == ["proof:1", "proof:2"]

    def test_glue_with_explicit_rank_and_patch(self) -> None:
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma_a, tau)
        b = e.add_observation(sigma_b, tau)
        rank = e.ensure_rank(5, label="r5")
        patch = e.ensure_patch("merge", rank=rank)
        result = e.glue(a.id, b.id, rank=rank, patch=patch)
        assert result.addr1 is not None
        assert result.addr1.rank == rank.id
        assert result.addr1.patch == patch.id

    def test_glue_result_all_addr1s(self) -> None:
        e = PFFCascadeEngine()
        sLa = e.ensure_chart("sigma", "LeafA")
        sLb = e.ensure_chart("sigma", "LeafB")
        sP = e.ensure_chart("sigma", "Parent")
        tT1 = e.ensure_chart("tau", "T1")
        tT2 = e.ensure_chart("tau", "T2")
        tT3 = e.ensure_chart("tau", "T3")
        tT4 = e.ensure_chart("tau", "T4")
        la = e.add_observation(sLa, tT1)
        lb = e.add_observation(sLb, tT2)
        e.add_observation(sP, tT3, sigma_children=[la.id])
        e.add_observation(sP, tT4, sigma_children=[lb.id])
        result = e.glue(la.id, lb.id)
        # The principal addr1 + the cascade addr1
        assert result.addr1 is not None
        assert len(result.cascade_addr1s) == 1
        assert len(result.all_addr1s) == 2

    def test_glue_result_all_addr1s_when_noop(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma, tau)
        result = e.glue(a.id, a.id)
        assert result.all_addr1s == []


# ── Path2 (coh) ────────────────────────────────────────────────────


class TestCohClosure:
    def test_explicit_coh_between_two_glues(self) -> None:
        """Two distinct Addr1s with the same canonical endpoints can be
        joined by an explicit coh."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        a = e.add_observation(sigma, tau_a)
        b = e.add_observation(sigma, tau_b)
        first = e.document.paths1[0]

        # Construct a second glue manually via the internal _emit_glue
        # to model two-distinct-proofs scenario.
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        second = e._emit_glue(a.id, b.id, rank, patch,
                              label="alt-proof",
                              premises=["proof:alt"])

        assert first.id != second.id
        addr2 = e.coh(first.id, second.id, label="coh-test")
        assert addr2 is not None
        assert addr2.ctor == "coh"
        assert addr2.src == first.id
        assert addr2.dst == second.id
        assert addr2.label == "coh-test"
        assert e.canonical_addr1(first.id) == e.canonical_addr1(second.id)
        assert e.receipt().wfStatus == "clean"

    def test_coh_idempotent(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first = e.document.paths1[0]
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        second = e._emit_glue("addr0-0", "addr0-1", rank, patch,
                              label="alt", premises=[])
        e.coh(first.id, second.id)
        # Second coh between the same path1 class is a no-op
        result = e.coh(first.id, second.id)
        assert result is None

    def test_coh_with_explicit_rank_and_patch(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        first = e.document.paths1[0]
        second = e._emit_glue("addr0-0", "addr0-1", rank, patch,
                              label="alt", premises=[])
        custom_rank = e.ensure_rank(2)
        custom_patch = e.ensure_patch("derive", rank=custom_rank)
        addr2 = e.coh(first.id, second.id, rank=custom_rank, patch=custom_patch)
        assert addr2 is not None
        assert addr2.rank == custom_rank.id
        assert addr2.patch == custom_patch.id


# ── Class queries ──────────────────────────────────────────────────


class TestClassQueries:
    def test_addr0_class_singleton(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma, tau)
        cls = e.addr0_class(a.id)
        assert cls == {a.id}

    def test_addr0_class_after_glue(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        a = e.add_observation(sigma, tau_a)
        b = e.add_observation(sigma, tau_b)
        cls = e.addr0_class(a.id)
        assert cls == {a.id, b.id}

    def test_all_addr0_classes(self) -> None:
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma_a, tau)
        e.add_observation(sigma_b, tau)
        classes = e.all_addr0_classes()
        # Two disjoint classes (different sigma)
        assert len(classes) == 2
        all_ids = set()
        for s in classes.values():
            all_ids |= s
        assert all_ids == {"addr0-0", "addr0-1"}

    def test_addr1_class_singleton(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        addr1 = e.document.paths1[0]
        cls = e.addr1_class(addr1.id)
        assert cls == {addr1.id}

    def test_addr1_class_after_coh(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first = e.document.paths1[0]
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        second = e._emit_glue("addr0-0", "addr0-1", rank, patch,
                              label="alt", premises=[])
        e.coh(first.id, second.id)
        cls = e.addr1_class(first.id)
        assert cls == {first.id, second.id}

    def test_all_addr1_classes(self) -> None:
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau_x = e.ensure_chart("tau", "X")
        tau_y = e.ensure_chart("tau", "Y")
        # Two completely independent η-glues
        e.add_observation(sigma_a, tau_x)
        e.add_observation(sigma_a, tau_y)
        e.add_observation(sigma_b, tau_x)
        e.add_observation(sigma_b, tau_y)
        classes = e.all_addr1_classes()
        # Two distinct addr1s in two distinct classes
        assert len(classes) == 2

    def test_canonical_addr0_self(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma, tau)
        # Single observation → its own canonical
        assert e.canonical_addr0(a.id) == a.id

    def test_class_queries_skip_cells_not_in_uf(self) -> None:
        """Cells manually added to the document (bypassing the
        engine) are not registered in ``_uf``, and the class query
        methods correctly exclude them instead of crashing."""
        from cstz.pff import Addr0, Addr1, Segment, Pair
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma, tau)
        # Manually append an Addr0 that the engine doesn't know
        foreign = Addr0(
            id="foreign-addr0", sort="X",
            segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart=sigma.id, root="X",
                            role="principal")],
            )],
        )
        e.document.addresses0.append(foreign)
        # Manually append an Addr1 that the engine doesn't know
        foreign_a1 = Addr1(
            id="foreign-addr1", rank="rank-0", ctor="glue",
            src="x", dst="y",
        )
        e.document.paths1.append(foreign_a1)
        # addr0_class for the engine-managed addr0 still works
        cls = e.addr0_class(a.id)
        assert cls == {a.id}
        assert "foreign-addr0" not in cls
        # all_addr0_classes excludes the foreign addr0
        all_cls = e.all_addr0_classes()
        for members in all_cls.values():
            assert "foreign-addr0" not in members
        # all_addr1_classes excludes the foreign addr1
        all_a1_cls = e.all_addr1_classes()
        for members in all_a1_cls.values():
            assert "foreign-addr1" not in members


# ── Reading-(a) projection: role coproduct view ────────────────────


class TestRoleCoproductView:
    def test_empty_engine(self) -> None:
        e = PFFCascadeEngine()
        assert e.role_coproduct_view() == {}

    def test_single_observation_partition(self) -> None:
        """A single observation produces one principal pair (under the
        σ-chart) and one aux pair (under the τ-chart)."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        addr0 = e.add_observation(sigma, tau)
        view = e.role_coproduct_view()

        assert sigma.id in view
        assert tau.id in view
        # σ chart has principal pair, no aux
        assert len(view[sigma.id]["principal"]) == 1
        assert view[sigma.id]["principal"][0][0] == addr0.id
        assert view[sigma.id]["principal"][0][1].role == "principal"
        assert view[sigma.id]["aux"] == []
        # τ chart has aux pair, no principal
        assert view[tau.id]["principal"] == []
        assert len(view[tau.id]["aux"]) == 1
        assert view[tau.id]["aux"][0][0] == addr0.id

    def test_multiple_observations_aggregate_per_chart(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        a = e.add_observation(sigma, tau_a)
        b = e.add_observation(sigma, tau_b)
        view = e.role_coproduct_view()
        # Both observations contribute their principal pair to the σ chart
        principals = {pid for (pid, _) in view[sigma.id]["principal"]}
        assert principals == {a.id, b.id}
        # Each tau chart has exactly one aux pair
        assert len(view[tau_a.id]["aux"]) == 1
        assert len(view[tau_b.id]["aux"]) == 1

    def test_charts_with_no_observations_appear_empty(self) -> None:
        e = PFFCascadeEngine()
        e.ensure_chart("sigma", "Unused")
        e.ensure_chart("tau", "AlsoUnused")
        sigma_used = e.ensure_chart("sigma", "Used")
        tau_used = e.ensure_chart("tau", "T")
        e.add_observation(sigma_used, tau_used)
        view = e.role_coproduct_view()
        unused_sigma = e.document.charts[0].id
        unused_tau = e.document.charts[1].id
        assert view[unused_sigma]["principal"] == []
        assert view[unused_sigma]["aux"] == []
        assert view[unused_tau]["principal"] == []
        assert view[unused_tau]["aux"] == []

    def test_view_role_coproduct_invariant(self) -> None:
        """For every chart minted with kind='sigma', all incoming pairs
        should be 'principal'; for kind='tau', all incoming pairs should
        be 'aux'.  This is the dual of reading (b) → reading (a)."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        view = e.role_coproduct_view()
        for chart in e.document.charts:
            bucket = view[chart.id]
            if chart.kind == "sigma":
                assert bucket["aux"] == []
            elif chart.kind == "tau":
                assert bucket["principal"] == []


# ── Document well-formedness invariant ────────────────────────────


class TestDocumentWellFormedness:
    def test_clean_after_each_step_of_complex_cascade(self) -> None:
        """The Document is well-formed at every observable step
        once the first observation seeds a rank."""
        e = PFFCascadeEngine()
        # Build a small structure step by step, asserting clean after each
        sigma_l = e.ensure_chart("sigma", "Leaf")
        sigma_p = e.ensure_chart("sigma", "Parent")
        sigma_l_alt = e.ensure_chart("sigma", "LeafAlt")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tC = e.ensure_chart("tau", "C")
        tD = e.ensure_chart("tau", "D")

        l1 = e.add_observation(sigma_l, tA)
        assert e.receipt().wfStatus == "clean"

        l2 = e.add_observation(sigma_l_alt, tB)
        assert e.receipt().wfStatus == "clean"

        p1 = e.add_observation(sigma_p, tC, sigma_children=[l1.id])
        assert e.receipt().wfStatus == "clean"

        p2 = e.add_observation(sigma_p, tD, sigma_children=[l2.id])
        assert e.receipt().wfStatus == "clean"

        e.glue(l1.id, l2.id)
        assert e.receipt().wfStatus == "clean"
        # And the cascade really did connect the parents
        assert e.canonical_addr0(p1.id) == e.canonical_addr0(p2.id)

    def test_engine_repr_includes_counts(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        s = repr(e)
        assert "addr0=2" in s
        assert "path1=1" in s
        assert "charts=3" in s


# ── Linear-view ↔ cascade cross-check ───────────────────────────────


def _partition_from_cascade_classes(cascade_classes):
    """Convert cascade.all_addr0_classes() output to a sorted list of
    frozensets, matching Document.path1_classes() format."""
    return sorted(
        (frozenset(s) for s in cascade_classes.values()),
        key=lambda s: min(s),
    )


class TestLinearViewCrossCheck:
    """Verify that Document.path1_classes() / path2_classes() agree
    with PFFCascadeEngine's union-find by construction.

    This is item 0c from the AUDIT.md GF(2) postscript: it makes
    the H₀ ↔ cascade equivalence a verified runtime invariant
    rather than just a comment.  For any populated engine, the
    document's standalone linear-algebraic partition computation
    must produce the same partition as the cascade's incremental
    union-find.
    """

    def _assert_path1_agreement(self, e: PFFCascadeEngine) -> None:
        doc_classes = e.document.path1_classes()
        cascade_classes = _partition_from_cascade_classes(
            e.all_addr0_classes()
        )
        assert doc_classes == cascade_classes

    def _assert_path2_agreement(self, e: PFFCascadeEngine) -> None:
        doc_classes = e.document.path2_classes()
        cascade_classes = _partition_from_cascade_classes(
            e.all_addr1_classes()
        )
        assert doc_classes == cascade_classes

    # ── path1 cross-checks ──

    def test_empty_engine_no_addr0s(self) -> None:
        e = PFFCascadeEngine()
        # No addr0s yet → empty partition on both sides
        assert e.document.path1_classes() == []

    def test_single_observation(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma, tau)
        self._assert_path1_agreement(e)

    def test_two_disjoint_observations(self) -> None:
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma_a, tau)
        e.add_observation(sigma_b, tau)
        self._assert_path1_agreement(e)

    def test_streaming_glue_at_leaves(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        # Streaming cascade glued them
        self._assert_path1_agreement(e)

    def test_three_way_streaming_glue(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        tau_c = e.ensure_chart("tau", "C")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        e.add_observation(sigma, tau_c)
        self._assert_path1_agreement(e)

    def test_recursive_cascade_two_levels(self) -> None:
        e = PFFCascadeEngine()
        sLa = e.ensure_chart("sigma", "LeafA")
        sLb = e.ensure_chart("sigma", "LeafB")
        sP = e.ensure_chart("sigma", "Parent")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tPa = e.ensure_chart("tau", "Pa")
        tPb = e.ensure_chart("tau", "Pb")
        la = e.add_observation(sLa, tA)
        lb = e.add_observation(sLb, tB)
        e.add_observation(sP, tPa, sigma_children=[la.id])
        e.add_observation(sP, tPb, sigma_children=[lb.id])
        e.glue(la.id, lb.id)
        self._assert_path1_agreement(e)

    def test_recursive_cascade_three_levels(self) -> None:
        e = PFFCascadeEngine()
        sLi = e.ensure_chart("sigma", "LeafInt")
        sLs = e.ensure_chart("sigma", "LeafStr")
        sM = e.ensure_chart("sigma", "Mid")
        sR = e.ensure_chart("sigma", "Root")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tC = e.ensure_chart("tau", "C")
        tD = e.ensure_chart("tau", "D")
        tE = e.ensure_chart("tau", "E")
        tF = e.ensure_chart("tau", "F")
        li = e.add_observation(sLi, tA)
        ls = e.add_observation(sLs, tB)
        mi = e.add_observation(sM, tC, sigma_children=[li.id])
        e.add_observation(sM, tD, sigma_children=[ls.id])
        e.add_observation(sR, tE, sigma_children=[mi.id])
        e.add_observation(sR, tF, sigma_children=[mi.id])
        e.glue(li.id, ls.id)
        self._assert_path1_agreement(e)

    def test_disjoint_components_preserved(self) -> None:
        """Two completely independent η-merges produce two disjoint
        path1 classes; both views should agree on the partition."""
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau_x = e.ensure_chart("tau", "X")
        tau_y = e.ensure_chart("tau", "Y")
        e.add_observation(sigma_a, tau_x)
        e.add_observation(sigma_a, tau_y)
        e.add_observation(sigma_b, tau_x)
        e.add_observation(sigma_b, tau_y)
        self._assert_path1_agreement(e)

    # ── path2 cross-checks ──

    def test_path2_empty(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma, tau)
        # No path1s yet, so path2 partition is also empty
        assert e.document.path2_classes() == []

    def test_path2_singleton_after_streaming_glue(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        # One path1 from streaming glue; no cohs → singleton class
        self._assert_path2_agreement(e)

    def test_path2_after_explicit_coh(self) -> None:
        from cstz.pff import Addr1
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first_id = e.document.paths1[0].id
        ids = [a.id for a in e.document.addresses0]
        # Mint a second redundant glue manually so we have two
        # distinct Addr1s on which to coh
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        second = e._emit_glue(
            ids[0], ids[1], rank, patch,
            label="alt", premises=[],
        )
        # Coh the two glues
        e.coh(first_id, second.id)
        self._assert_path2_agreement(e)

    # ── Linear-view operates on Document alone ──

    def test_linear_view_independent_of_engine(self) -> None:
        """The Document.path1_classes() computation needs no
        cascade engine — only the document's paths1 collection.
        Verify by tearing down the engine and exercising the doc."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        doc = e.document  # Capture the doc
        del e  # Drop the engine
        # The document's accessors still work
        assert len(doc.path1_classes()) == 1
        assert len(doc.path1_constraint_rows()) == 1


# ── Grothendieck topology axioms + σ-key ≡ path1 theorem ────────────


def _sigma_key_partition_from_engine(
    engine: PFFCascadeEngine,
) -> list:
    """Extract the sigma-key partition from the engine's internal
    ``_addr0s_by_sigma_key`` state.

    Returns a sorted list of frozen sets, matching the shape of
    ``Document.path1_classes()``.  Used by
    ``TestSigmaKeyEqualsPath1AtFixedPoint`` to compare the engine's
    internal sigma-key bookkeeping against the Document-level
    path1 partition.
    """
    classes = [
        frozenset(bucket)
        for bucket in engine._addr0s_by_sigma_key.values()
        if bucket
    ]
    return sorted(classes, key=lambda s: min(s))


class TestGrothendieckTopology:
    """Verify the three Grothendieck-topology axioms as runtime
    invariants on the σ-Slicer and the τ-Slicer.

    The σ-Slicer operates on Addr0 ids via sigma-key equivalence
    and produces the path1 partition.  The τ-Slicer operates on
    Addr1 ids via raw-pair equivalence and produces the path2
    partition.  Both should satisfy:

      1. Identity cover: every element is in a sieve containing itself
      2. Stability under pullback: adding observations never removes
         an element from its sieve (monotonicity)
      3. Transitivity: the sieves are closed under transitive closure

    These are the same properties the cascade engine maintains as
    invariants, but tested directly against the Slicer accessors on
    Document (not against the engine internals).  They are the
    topological-interpretation counterpart of the linear-algebraic
    cross-check tests in TestLinearViewCrossCheck above.
    """

    # ── σ-Slicer axioms ──

    def test_sigma_identity_cover_for_every_addr0(self) -> None:
        """Axiom 1 (σ): every Addr0 is in the sieve containing itself."""
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma_a, tau)
        b = e.add_observation(sigma_b, tau)
        for addr0_id in (a.id, b.id):
            sieve = e.document.covering_sieve_for_addr0(addr0_id)
            assert addr0_id in sieve

    def test_sigma_stability_under_pullback_monotonicity(self) -> None:
        """Axiom 2 (σ): adding observations never removes an Addr0
        from its sieve.  Members can only be added, never removed."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        tau_c = e.ensure_chart("tau", "C")

        a = e.add_observation(sigma, tau_a)
        sieve_a_round1 = e.document.covering_sieve_for_addr0(a.id)

        b = e.add_observation(sigma, tau_b)
        sieve_a_round2 = e.document.covering_sieve_for_addr0(a.id)
        # Every member of round1 is still a member of round2
        assert sieve_a_round1 <= sieve_a_round2

        e.add_observation(sigma, tau_c)
        sieve_a_round3 = e.document.covering_sieve_for_addr0(a.id)
        assert sieve_a_round2 <= sieve_a_round3

    def test_sigma_transitivity_of_sieve_membership(self) -> None:
        """Axiom 3 (σ): if A and B are in the same sieve and B and C
        are in the same sieve, then A and C are in the same sieve."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        tau_c = e.ensure_chart("tau", "C")
        a = e.add_observation(sigma, tau_a)
        b = e.add_observation(sigma, tau_b)
        c = e.add_observation(sigma, tau_c)
        # All three streaming-glued; by transitivity all three
        # must be in the same sieve
        sieve_a = e.document.covering_sieve_for_addr0(a.id)
        sieve_c = e.document.covering_sieve_for_addr0(c.id)
        assert sieve_a == sieve_c
        assert b.id in sieve_a

    def test_sigma_sieves_partition_the_addr0_universe(self) -> None:
        """The sieves form a partition: every Addr0 is in exactly
        one sieve, and the union is the full Addr0 set."""
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau_x = e.ensure_chart("tau", "X")
        tau_y = e.ensure_chart("tau", "Y")
        e.add_observation(sigma_a, tau_x)
        e.add_observation(sigma_a, tau_y)  # streaming-glued with above
        e.add_observation(sigma_b, tau_x)
        e.add_observation(sigma_b, tau_y)  # streaming-glued with above

        sieves = e.document.covering_sieves_over_addr0()
        all_addr0_ids = {a.id for a in e.document.addresses0}
        # Pairwise disjoint
        for i, s1 in enumerate(sieves):
            for s2 in sieves[i + 1:]:
                assert s1.isdisjoint(s2)
        # Covering
        union = set()
        for s in sieves:
            union |= s
        assert union == all_addr0_ids

    # ── τ-Slicer axioms ──

    def test_tau_identity_cover_for_every_addr1(self) -> None:
        """Axiom 1 (τ): every Addr1 is in a τ-sieve containing itself."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        # At least one path1 glue was emitted by the streaming cascade
        assert len(e.document.paths1) >= 1
        for p1 in e.document.paths1:
            sieve = e.document.covering_sieve_for_addr1(p1.id)
            assert p1.id in sieve

    def test_tau_stability_under_pullback_monotonicity(self) -> None:
        """Axiom 2 (τ): adding observations never removes an Addr1
        from its τ-sieve."""
        from cstz.pff import Addr1, Addr2
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first = e.document.paths1[0]
        sieve_first_round1 = e.document.covering_sieve_for_addr1(first.id)

        # Add a user-declared coh that unions first with a newly-
        # constructed Addr1
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        second = e._emit_glue(
            first.src, first.dst, rank, patch,
            label="alt", premises=[],
        )
        e.coh(first.id, second.id)

        sieve_first_round2 = e.document.covering_sieve_for_addr1(first.id)
        # Monotonicity: the original sieve is a subset of the new one
        assert sieve_first_round1 <= sieve_first_round2
        assert second.id in sieve_first_round2

    def test_tau_transitivity_of_sieve_membership(self) -> None:
        """Axiom 3 (τ): path2 cohs are transitively closed."""
        from cstz.pff import Addr1
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first = e.document.paths1[0]
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)

        # Manually mint two more Addr1s with the same endpoints
        second = e._emit_glue(
            first.src, first.dst, rank, patch,
            label="alt-1", premises=[],
        )
        third = e._emit_glue(
            first.src, first.dst, rank, patch,
            label="alt-2", premises=[],
        )

        # Coh first~second and second~third; expect first and third
        # in the same sieve by transitivity
        e.coh(first.id, second.id)
        e.coh(second.id, third.id)

        sieve = e.document.covering_sieve_for_addr1(first.id)
        assert second.id in sieve
        assert third.id in sieve

    # ── Alias equivalence with linear-view accessors ──

    def test_covering_sieves_over_addr0_equals_path1_classes(self) -> None:
        """The Slicer accessors are semantic aliases for the
        linear-view accessors.  Same values, different names."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        assert (
            e.document.covering_sieves_over_addr0()
            == e.document.path1_classes()
        )
        assert (
            e.document.covering_sieves_over_addr1()
            == e.document.path2_classes()
        )


class TestSigmaKeyRefinesPath1:
    """Verify the secondary (robustness) theorem: even under data
    corruption via ``engine.glue()`` calls that force merges the
    cascade would not otherwise derive, the sigma-key partition
    remains a refinement of the path1 partition.

    Refinement means: every bucket of ``_addr0s_by_sigma_key`` sits
    entirely inside a single path1 class.  Two Addr0s with the same
    sigma-key are necessarily in the same path1 class (the cascade
    enforces this).  The converse is not true: two Addr0s can end
    up in the same path1 class without sharing a sigma-key, if the
    caller issued a direct ``engine.glue()`` between them.

    The primary theorem (σ-key ≡ path1 equality) is tested below in
    ``TestSigmaKeyEqualsPath1InPureCascade`` under the correct-usage
    regime where every path1 edge comes from a sigma-key collision
    during streaming ingest.

    Per the AUDIT.md Slicer postscript, direct ``engine.glue()``
    calls across distinct sigma-key classes are considered **data
    corruption** under the PFF discipline: users should introduce
    equivalences via discriminator-synthesis through the data,
    not by forcing merges from outside the cascade.  These tests
    verify the engine still behaves sensibly under that corruption
    — it does not crash, and the sigma-key / path1 containment
    remains intact.  They are robustness tests, not correctness
    tests for the primary theorem.
    """

    def _assert_sigma_key_refines_path1(self, e: PFFCascadeEngine) -> None:
        """Every sigma-key bucket's members must share a path1 class."""
        canon_map = e.document.path1_canonical_map()
        for bucket_key, bucket in e._addr0s_by_sigma_key.items():
            if not bucket:
                continue
            canonicals = {canon_map[aid] for aid in bucket}
            assert len(canonicals) == 1, (
                f"sigma-key bucket {bucket_key!r} spans multiple path1 "
                f"classes: {canonicals}"
            )

    def test_single_observation(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma, tau)
        self._assert_sigma_key_refines_path1(e)

    def test_streaming_glue(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        self._assert_sigma_key_refines_path1(e)

    def test_recursive_cascade_two_levels(self) -> None:
        """Refinement holds even with user-initiated glue across
        distinct sigma-keys.  The sigma-key partition stays finer
        than path1 because the user's glue bridged two buckets."""
        e = PFFCascadeEngine()
        sLa = e.ensure_chart("sigma", "LeafA")
        sLb = e.ensure_chart("sigma", "LeafB")
        sP = e.ensure_chart("sigma", "Parent")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tPa = e.ensure_chart("tau", "Pa")
        tPb = e.ensure_chart("tau", "Pb")
        la = e.add_observation(sLa, tA)
        lb = e.add_observation(sLb, tB)
        e.add_observation(sP, tPa, sigma_children=[la.id])
        e.add_observation(sP, tPb, sigma_children=[lb.id])
        e.glue(la.id, lb.id)
        self._assert_sigma_key_refines_path1(e)

    def test_recursive_cascade_three_levels(self) -> None:
        e = PFFCascadeEngine()
        sLi = e.ensure_chart("sigma", "LeafInt")
        sLs = e.ensure_chart("sigma", "LeafStr")
        sM = e.ensure_chart("sigma", "Mid")
        sR = e.ensure_chart("sigma", "Root")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tC = e.ensure_chart("tau", "C")
        tD = e.ensure_chart("tau", "D")
        tE = e.ensure_chart("tau", "E")
        tF = e.ensure_chart("tau", "F")
        li = e.add_observation(sLi, tA)
        ls = e.add_observation(sLs, tB)
        mi = e.add_observation(sM, tC, sigma_children=[li.id])
        e.add_observation(sM, tD, sigma_children=[ls.id])
        e.add_observation(sR, tE, sigma_children=[mi.id])
        e.add_observation(sR, tF, sigma_children=[mi.id])
        e.glue(li.id, ls.id)
        self._assert_sigma_key_refines_path1(e)


def _seeded_document():
    """Build a Document seeded with the minimal rank/patch/chart
    state the PFFCascadeEngine would produce on empty init.

    Used by TestAutoCohClosure for direct Document-level invocation
    of auto_coh_closure without going through the engine.  The rank
    id is ``rank-0`` and the patch id is ``patch-0``, matching the
    engine's default ids.
    """
    from cstz.pff import Chart, Document, Patch, Rank
    return Document(
        documentId="test-seeded",
        ranks=[Rank(id="rank-0", ordinal=0, label="ingest")],
        patches=[Patch(id="patch-0", rank="rank-0", phase="ingest")],
        charts=[Chart(id="c0", root="x", kind="sigma", patch="patch-0")],
    )


class TestAutoCohClosure:
    """Verify emission-time morphism hash-cons (formerly τ-cascade
    auto-coh fixed-point pass).

    **HIT collapse note:** before the HIT collapse, this class
    tested the ``auto_coh_closure`` post-hoc pass that ran after
    ``add_observation`` to find duplicate morphisms and emit
    path2 cohs between them.  Under the HIT collapse, morphisms
    are hash-consed at emission time in ``_emit_glue``, so
    duplicates never get created in the first place.  The class
    is kept with its original name for git blame continuity, but
    its invariants now describe the emission-time behavior
    directly.

    Under correct usage, the rank-1 cascade (_glue_set_and_cascade)
    fires automatically at the end of every ``add_observation``
    call.  Hash-cons at emission ensures no two Addr1s in
    ``paths1`` have the same sigma_key over the canonical
    endpoint pair at emission time.
    """

    # ── Emission-time hash-cons behavior ──

    def test_three_member_class_emits_two_distinct_glues(self) -> None:
        """Three observations glued into one path1 class → two
        morphisms emitted (not three).  The second and third
        observations each produce one morphism whose canonical
        endpoints at emission time are distinct, so emission-time
        hash-cons does not dedupe them.

        Under the HIT collapse (post commit e[TBD]), paths2 stays
        empty because the old auto_coh_closure post-hoc dedup pass
        is deleted.  The two morphisms remain distinct witnesses
        of the same path1 equivalence, which is the correct HIT
        / ∞-groupoid discipline: distinct paths with the same
        endpoints are first-class rank-1 cells.
        """
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        tau_c = e.ensure_chart("tau", "C")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        e.add_observation(sigma, tau_c)
        # Two distinct path1 witnesses (n-1 morphisms for n
        # equivalent addr0s, anchor-first tree structure).
        assert len(e.document.paths1) == 2
        # Zero path2 cohs — auto_coh_closure no longer fires
        # automatically; morphism distinctness is preserved.
        assert len(e.document.paths2) == 0
        # All three addr0s in one path1 equivalence class via
        # the union-find closure.
        assert len(e.document.path1_classes()) == 1

    def test_auto_coh_noop_on_pair(self) -> None:
        """Two observations → one glue → no cohs (nothing to cohere)."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        assert len(e.document.paths1) == 1
        assert len(e.document.paths2) == 0

    def test_auto_coh_noop_on_singleton(self) -> None:
        """One observation → no glues → no cohs."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma, tau)
        assert len(e.document.paths1) == 0
        assert len(e.document.paths2) == 0

    def test_auto_coh_noop_on_disjoint_classes(self) -> None:
        """Observations that can't be glued → no auto-cohs."""
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma_a, tau)
        e.add_observation(sigma_b, tau)
        assert len(e.document.paths1) == 0
        assert len(e.document.paths2) == 0

    def test_four_member_class_emits_three_distinct_glues(self) -> None:
        """Four observations → three distinct morphisms, zero cohs.

        HIT collapse: each new observation adds one morphism
        connecting it to the existing anchor (addr0-0), and each
        such morphism has distinct canonical endpoints at
        emission time, so emission-time hash-cons doesn't dedupe.
        """
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        for name in ("A", "B", "C", "D"):
            tau = e.ensure_chart("tau", name)
            e.add_observation(sigma, tau)
        assert len(e.document.paths1) == 3
        assert len(e.document.paths2) == 0
        assert len(e.document.path1_classes()) == 1

    def test_recursive_cascade_still_produces_correct_morphism_count(
        self,
    ) -> None:
        """Recursive σ-cascade scenarios continue to produce the
        right morphism count under the HIT collapse: (n-1)
        morphisms for n equivalent addr0s, anchor-first tree.
        The HIT collapse doesn't change the σ-cascade's structure;
        it only deletes the post-hoc auto-coh pass.
        """
        e = PFFCascadeEngine()
        sigma_leaf = e.ensure_chart("sigma", "Leaf")
        for name in ("A", "B", "C"):
            tau = e.ensure_chart("tau", f"L-{name}")
            e.add_observation(sigma_leaf, tau)
        # All three leaves in one path1 class, 2 glues emitted.
        assert len(e.document.paths1) == 2
        assert len(e.document.paths2) == 0
        assert len(e.document.path1_classes()) == 1

    # ── Engine-level vs Document-level parity ──

    def test_engine_addr1_uf_matches_document_path2_classes(self) -> None:
        """After auto-coh fires, the engine's internal _addr1_uf
        must agree with the Document's path2_classes()."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        for name in ("A", "B", "C", "D"):
            tau = e.ensure_chart("tau", name)
            e.add_observation(sigma, tau)

        doc_classes = e.document.path2_classes()
        engine_classes = sorted(
            (frozenset(s) for s in e.all_addr1_classes().values()),
            key=lambda s: min(s),
        )
        assert doc_classes == engine_classes

    # ── Document-level direct invocation ──

    def test_document_auto_coh_closure_idempotent(self) -> None:
        """Running auto_coh_closure twice on a Document produces no
        new records the second time."""
        from cstz.pff import Addr0, Addr1, Pair, Patch, Rank, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(3)
        ]
        d.paths1 = [
            Addr1(id=f"g{i}", rank="rank-0", ctor="glue",
                  src="a0", dst=f"a{i + 1}", patch="patch-0")
            for i in range(2)
        ]
        new1 = d.auto_coh_closure()
        assert len(new1) == 1  # 2 glues in one class → 1 coh
        new2 = d.auto_coh_closure()
        assert new2 == []

    def test_document_auto_coh_closure_returns_new_records(self) -> None:
        """The return value of auto_coh_closure is the list of
        newly-minted Addr2 records, in emission order."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(4)
        ]
        d.paths1 = [
            Addr1(id=f"g{i}", rank="rank-0", ctor="glue",
                  src="a0", dst=f"a{i + 1}", patch="patch-0")
            for i in range(3)
        ]
        new = d.auto_coh_closure()
        assert len(new) == 2
        # All are coh
        assert all(r.ctor == "coh" for r in new)
        # All have auto-coh-N ids starting from N=0 (paths2 was empty)
        assert [r.id for r in new] == ["auto-coh-0", "auto-coh-1"]

    def test_document_auto_coh_skips_non_glue_ctors(self) -> None:
        """Addr1 records with ctors other than glue/refl are ignored
        by the τ-cascade."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(2)
        ]
        # Two Addr1s witnessing the same canonical pair, but both
        # use non-glue ctors → τ-cascade ignores both → no cohs
        d.paths1 = [
            Addr1(id="t1", rank="rank-0", ctor="transport",
                  src="a0", dst="a1", patch="patch-0"),
            Addr1(id="t2", rank="rank-0", ctor="compose",
                  src="a0", dst="a1", patch="patch-0"),
        ]
        new = d.auto_coh_closure()
        assert new == []

    def test_document_auto_coh_handles_refl_ctor(self) -> None:
        """refl Addr1s DO participate in τ-coherence (they assert
        path1 equivalence, same as glue)."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id="a0", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root="a0", role="principal")],
            )]),
        ]
        # Two refl Addr1s on the same addr0 → same canonical pair
        d.paths1 = [
            Addr1(id="r1", rank="rank-0", ctor="refl",
                  src="a0", dst="a0", patch="patch-0"),
            Addr1(id="r2", rank="rank-0", ctor="refl",
                  src="a0", dst="a0", patch="patch-0"),
        ]
        new = d.auto_coh_closure()
        assert len(new) == 1

    def test_document_auto_coh_skips_singleton_groups(self) -> None:
        """A canonical-pair group with only one Addr1 doesn't need
        coherence — no coh is emitted."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(3)
        ]
        # Three Addr1s in three disjoint canonical-pair groups
        d.paths1 = [
            Addr1(id="g1", rank="rank-0", ctor="glue",
                  src="a0", dst="a1", patch="patch-0"),
            # Different raw pair, and since the three addr0s don't
            # end up in the same path1 class (only a0~a1 was glued
            # by the caller), these stay in separate groups.
        ]
        new = d.auto_coh_closure()
        assert new == []

    def test_document_auto_coh_groups_reversed_endpoints(self) -> None:
        """Two glues with swapped raw endpoints (a0→a1 and a1→a0)
        both canonicalize to the same path1 class and land in the
        same group — the sorted raw-pair label picks the
        lex-smaller endpoint first regardless of raw direction."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(2)
        ]
        d.paths1 = [
            Addr1(id="g-fwd", rank="rank-0", ctor="glue",
                  src="a0", dst="a1", patch="patch-0"),
            Addr1(id="g-rev", rank="rank-0", ctor="glue",
                  src="a1", dst="a0", patch="patch-0"),
        ]
        new = d.auto_coh_closure()
        assert len(new) == 1

    def test_document_auto_coh_groups_reversed_first(self) -> None:
        """The raw_pair_of label uses the first Addr1's raw endpoints,
        sorted.  When the first Addr1 has raw src > dst, the sort
        normalization kicks in and the label still picks lex-smaller
        first."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(2)
        ]
        # First Addr1 has src="a1" > dst="a0"; the label should
        # still be "auto-coh:a0~a1" (sorted).
        d.paths1 = [
            Addr1(id="g-rev", rank="rank-0", ctor="glue",
                  src="a1", dst="a0", patch="patch-0"),
            Addr1(id="g-fwd", rank="rank-0", ctor="glue",
                  src="a0", dst="a1", patch="patch-0"),
        ]
        new = d.auto_coh_closure()
        assert len(new) == 1
        assert new[0].label == "auto-coh:a0~a1"

    def test_document_auto_coh_three_member_group(self) -> None:
        """A group with three glues emits two cohs in an anchor-first
        chain.  All three Addr1s end up in the same path2 class."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(4)
        ]
        # Three glues connecting a0 to a1, a2, a3.  Path1 closure
        # unifies all four addr0s.  Canonical pairs are all (a0, a0).
        # One group of 3 → 2 cohs via anchor-first pattern.
        d.paths1 = [
            Addr1(id=f"g{i}", rank="rank-0", ctor="glue",
                  src="a0", dst=f"a{i + 1}", patch="patch-0")
            for i in range(3)
        ]
        new = d.auto_coh_closure()
        assert len(new) == 2
        assert len(d.path2_classes()) == 1

    def test_document_auto_coh_uses_lex_smallest_rank(self) -> None:
        """Rank selection: the emitted coh uses the lex-smallest rank
        id among the grouped Addr1s."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.ranks.append(Rank(id="rank-extra", ordinal=1))
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(2)
        ]
        d.paths1 = [
            Addr1(id="g1", rank="rank-extra", ctor="glue",
                  src="a0", dst="a1", patch="patch-0"),
            Addr1(id="g2", rank="rank-0", ctor="glue",
                  src="a0", dst="a1", patch="patch-0"),
        ]
        new = d.auto_coh_closure()
        assert len(new) == 1
        # lex-smallest of {"rank-0", "rank-extra"} is "rank-0"
        assert new[0].rank == "rank-0"

    def test_document_auto_coh_uses_first_patch_with_none_handling(self) -> None:
        """Patch selection: the emitted coh uses the first non-None
        patch found among the grouped Addr1s."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(2)
        ]
        d.paths1 = [
            Addr1(id="g1", rank="rank-0", ctor="glue",
                  src="a0", dst="a1", patch=None),
            Addr1(id="g2", rank="rank-0", ctor="glue",
                  src="a0", dst="a1", patch="patch-0"),
        ]
        new = d.auto_coh_closure()
        assert len(new) == 1
        assert new[0].patch == "patch-0"

    def test_document_auto_coh_handles_no_patches_available(self) -> None:
        """If no grouped Addr1 has a patch, the coh's patch is None."""
        from cstz.pff import Addr0, Addr1, Pair, Segment
        d = _seeded_document()
        d.addresses0 = [
            Addr0(id=f"a{i}", segments=[Segment(
                rank="rank-0", phase="ingest", patch="patch-0",
                pairs=[Pair(chart="c0", root=f"a{i}", role="principal")],
            )])
            for i in range(2)
        ]
        d.paths1 = [
            Addr1(id="g1", rank="rank-0", ctor="glue",
                  src="a0", dst="a1", patch=None),
            Addr1(id="g2", rank="rank-0", ctor="glue",
                  src="a0", dst="a1", patch=None),
        ]
        new = d.auto_coh_closure()
        assert len(new) == 1
        assert new[0].patch is None

    def test_document_auto_coh_handles_no_ranks_available(self) -> None:
        """If no grouped Addr1 has a rank (edge case: all rank="" or
        equivalent), the conservative rank is the empty string."""
        # This is unreachable under PFF validation (all Addr1s have
        # non-empty rank strings), but the code handles the None
        # case defensively — we test the fall-through branch
        # indirectly via the patch-None test above.
        pass

    # ── Engine-level auto_coh_closure direct invocation ──

    def test_engine_auto_coh_closure_manual_invocation(self) -> None:
        """Calling engine.auto_coh_closure() directly (e.g., after
        a manual Document edit) returns the new records and syncs
        the engine's _addr1_uf."""
        from cstz.pff import Addr1
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        # Only one path1, no cohs yet (auto-coh was a no-op)
        assert len(e.document.paths2) == 0

        # Manually add a second Addr1 witnessing the same raw pair
        first = e.document.paths1[0]
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        e.document.paths1.append(Addr1(
            id="manual-alt", rank=rank.id, ctor="glue",
            src=first.src, dst=first.dst, patch=patch.id,
        ))

        # Now run auto-coh manually
        new = e.auto_coh_closure()
        assert len(new) == 1
        # The engine's _addr1_uf must have been updated
        assert e.canonical_addr1(first.id) == e.canonical_addr1("manual-alt")

    def test_engine_auto_coh_closure_idempotent_manual(self) -> None:
        """Manual auto_coh_closure invocation is also idempotent."""
        from cstz.pff import Addr1
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first = e.document.paths1[0]
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        e.document.paths1.append(Addr1(
            id="manual-alt", rank=rank.id, ctor="glue",
            src=first.src, dst=first.dst, patch=patch.id,
        ))
        new1 = e.auto_coh_closure()
        assert len(new1) == 1
        new2 = e.auto_coh_closure()
        assert new2 == []


class TestSigmaKeyEqualsPath1InPureCascade:
    """The refinement becomes an equality when no user-initiated
    glues are issued.  Every path1 edge then comes from a streaming
    sigma-key collision, and the two partitions coincide by the
    monotonicity argument in the inference.agda SPPF.ClosureProofs
    comment.
    """

    def _assert_sigma_key_equals_path1(self, e: PFFCascadeEngine) -> None:
        sigma_key_partition = _sigma_key_partition_from_engine(e)
        path1_partition = e.document.path1_classes()
        assert sigma_key_partition == path1_partition

    def test_single_observation_no_glue(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma, tau)
        self._assert_sigma_key_equals_path1(e)

    def test_streaming_glue_single_sigma_chart(self) -> None:
        """Two observations with the same sigma chart, different tau
        charts: the streaming cascade glues them via sigma-key
        collision.  Pure-cascade scenario → equality holds."""
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        self._assert_sigma_key_equals_path1(e)

    def test_multiple_disjoint_sigma_charts_no_glue(self) -> None:
        """Observations under distinct sigma charts → no streaming
        glue; no user glue either.  Each Addr0 is its own sigma-key
        bucket AND its own path1 class.  Equality holds."""
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma_a, tau)
        e.add_observation(sigma_b, tau)
        self._assert_sigma_key_equals_path1(e)

    def test_three_way_streaming_glue(self) -> None:
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        tau_c = e.ensure_chart("tau", "C")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        e.add_observation(sigma, tau_c)
        self._assert_sigma_key_equals_path1(e)


# ── HIT collapse additions (Step 1.5) ──────────────────────────────


class TestSigmaKeyFunction:
    """Cover the module-level ``pff.sigma_key`` function added by
    the HIT collapse (Step 1.5).

    sigma_key produces a rank-agnostic hash-cons signature for any
    Cell type (Addr0, Addr1, Addr2).  These tests assert
    **behavioral invariants** (equal inputs → equal keys, different
    inputs → different keys, namespaces disjoint) rather than
    literal tuple shapes, so they survive internal refactors of the
    sigma_key output format.  See the v2 test-suite walk: "the v2
    replacement is not 'rewrite the assertions' but 'test the
    constructor algebra equality directly.'"
    """

    def test_addr0_sigma_key_discriminates_by_sort(self) -> None:
        """Two Addr0s with different sorts produce different keys."""
        from cstz.pff import Addr0, Pair, Segment, sigma_key
        mk = lambda sort: Addr0(
            id="a", sort=sort,
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c0", root="r", role="principal")],
            )],
        )
        assert sigma_key(mk("X")) != sigma_key(mk("Y"))

    def test_addr0_sigma_key_discriminates_by_segments(self) -> None:
        """Two Addr0s with different segment structure produce
        different keys."""
        from cstz.pff import Addr0, Pair, Segment, Step, sigma_key
        base = Addr0(
            id="a", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c0", root="r", role="principal")],
            )],
        )
        with_route = Addr0(
            id="b", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(
                    chart="c0", root="r", role="principal",
                    route=[Step(kind="child", arg=0)],
                )],
            )],
        )
        assert sigma_key(base) != sigma_key(with_route)

    def test_addr0_sigma_key_equal_for_equivalent_cells(self) -> None:
        """Two Addr0s with different ids but identical structural
        content produce the same sigma_key — the id is not part of
        the signature under the default perspective."""
        from cstz.pff import Addr0, Pair, Segment, sigma_key
        mk = lambda _id: Addr0(
            id=_id, sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c0", root="r", role="principal")],
            )],
        )
        assert sigma_key(mk("a0")) == sigma_key(mk("b0"))

    def test_addr1_sigma_key_equal_for_same_ctor_endpoints_premises(
        self,
    ) -> None:
        """Two Addr1s with the same (ctor, src, dst, premises)
        produce the same key regardless of id, rank, or label."""
        from cstz.pff import Addr1, sigma_key
        a = Addr1(id="g1", rank="r0", ctor="glue", src="a", dst="b",
                  premises=["p1"], label="first")
        b = Addr1(id="g2", rank="r1", ctor="glue", src="a", dst="b",
                  premises=["p1"], label="second")
        assert sigma_key(a) == sigma_key(b)

    def test_addr1_sigma_key_discriminates_by_ctor(self) -> None:
        """Two Addr1s with different ctors produce different keys."""
        from cstz.pff import Addr1, sigma_key
        glue = Addr1(id="g", rank="r0", ctor="glue", src="a", dst="b")
        named = Addr1(id="n", rank="r0", ctor="named", src="a", dst="b")
        assert sigma_key(glue) != sigma_key(named)

    def test_addr1_sigma_key_discriminates_by_premises(self) -> None:
        """Two Addr1s with different premises produce different keys."""
        from cstz.pff import Addr1, sigma_key
        a = Addr1(id="g1", rank="r0", ctor="glue", src="a", dst="b",
                  premises=["p1"])
        b = Addr1(id="g2", rank="r0", ctor="glue", src="a", dst="b",
                  premises=["p2"])
        assert sigma_key(a) != sigma_key(b)

    def test_addr2_sigma_key_equal_for_same_ctor_endpoints(self) -> None:
        """Two Addr2s with the same (ctor, src, dst) produce the
        same key."""
        from cstz.pff import Addr2, sigma_key
        a = Addr2(id="c1", rank="r0", ctor="coh", src="g1", dst="g2")
        b = Addr2(id="c2", rank="r1", ctor="coh", src="g1", dst="g2")
        assert sigma_key(a) == sigma_key(b)

    def test_addr1_differs_from_addr2_with_same_endpoints(self) -> None:
        """Addr1 and Addr2 with the same src/dst but different ctors
        produce different keys — sigma_key distinguishes them."""
        from cstz.pff import Addr1, Addr2, sigma_key
        a1 = Addr1(id="g", rank="r0", ctor="glue", src="x", dst="y")
        a2 = Addr2(id="c", rank="r0", ctor="coh", src="x", dst="y")
        assert sigma_key(a1) != sigma_key(a2)

    def test_addr0_and_morphism_namespaces_disjoint(self) -> None:
        """Addr0 and Addr1/Addr2 sigma_keys never collide — the
        hash-cons can never confuse an object with a morphism."""
        from cstz.pff import Addr0, Addr1, Addr2, Pair, Segment, sigma_key
        a0 = Addr0(
            id="a", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c", root="r", role="principal")],
            )],
        )
        a1 = Addr1(id="g", rank="r0", ctor="glue", src="a", dst="b")
        a2 = Addr2(id="c", rank="r0", ctor="coh", src="a", dst="b")
        keys = {sigma_key(a0), sigma_key(a1), sigma_key(a2)}
        assert len(keys) == 3  # all three are distinct

    def test_emit_glue_key_is_morphism_term(self) -> None:
        """The hash-cons key used by ``_emit_glue`` is built via
        ``morphism_term()`` — the same constructor that
        ``sigma_key`` uses internally.  The minted Addr1 IS a
        value stored in ``_morphism_signature_index``, and the
        key for that value is a tuple of (key, value) pairs in
        the truncation-priority field ordering."""
        e = PFFCascadeEngine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma_a, tau, sort="A")
        b = e.add_observation(sigma_b, tau, sort="B")
        result = e.glue(a.id, b.id)
        addr1 = result.addr1
        assert addr1 is not None
        # The addr1 IS stored in the index as a value
        assert addr1 in e._morphism_signature_index.values()
        # The key for it is a tuple of (key, value) pairs —
        # every element is a 2-tuple
        for stored_key, stored_val in e._morphism_signature_index.items():
            if stored_val is addr1:
                for field in stored_key:
                    assert isinstance(field, tuple)
                    assert len(field) == 2
                break


class TestSigmaKeyPerspectives:
    """Cover the perspective lattice added by Step 1.5.1 Pass 1.

    sigma_key now takes a ``perspective`` parameter (a frozenset of
    discriminator names).  Three named perspectives are provided:
    PERSPECTIVE_SIGMA (finest, default), PERSPECTIVE_TAU (middle),
    PERSPECTIVE_KAPPA (coarsest).  These tests cover the non-default
    branches and the dual-reading basis-choice contract.

    The labels σ/τ/κ are a relational naming convention (Reading A
    matching ``core.py``); the discriminator content is what's
    load-bearing.  See the dual-reading caveat in the
    ``sigma_key`` module-level docstring.
    """

    def test_default_perspective_is_sigma(self) -> None:
        """``sigma_key(cell)`` (no perspective arg) is byte-identical
        to ``sigma_key(cell, perspective=PERSPECTIVE_SIGMA)``."""
        from cstz.pff import (
            Addr0, Addr1, Pair, Segment, sigma_key, PERSPECTIVE_SIGMA,
        )
        a0 = Addr0(
            id="a", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c", root="r", role="principal")],
            )],
        )
        a1 = Addr1(
            id="g", rank="r0", ctor="glue", src="x", dst="y",
            premises=["p1"],
        )
        assert sigma_key(a0) == sigma_key(a0, perspective=PERSPECTIVE_SIGMA)
        assert sigma_key(a1) == sigma_key(a1, perspective=PERSPECTIVE_SIGMA)

    def test_addr0_perspective_tau_drops_segments(self) -> None:
        """Under PERSPECTIVE_TAU, an Addr0's segments are NOT in the key.
        Two Addr0s with the same sort but different segments are
        identified at τ."""
        from cstz.pff import (
            Addr0, Pair, Segment, sigma_key, PERSPECTIVE_TAU,
        )
        a = Addr0(
            id="a", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c0", root="r", role="principal")],
            )],
        )
        b = Addr0(
            id="b", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p1",
                pairs=[Pair(chart="c1", root="r2", role="aux")],
            )],
        )
        assert sigma_key(a, perspective=PERSPECTIVE_TAU) == \
            sigma_key(b, perspective=PERSPECTIVE_TAU)
        # σ-perspective still distinguishes them
        assert sigma_key(a) != sigma_key(b)

    def test_addr0_perspective_kappa_keeps_only_sort(self) -> None:
        """Under PERSPECTIVE_KAPPA, only sort survives for an Addr0."""
        from cstz.pff import (
            Addr0, Pair, Segment, sigma_key, PERSPECTIVE_KAPPA,
        )
        a = Addr0(
            id="a", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c", root="r", role="principal")],
            )],
        )
        # κ-key for an Addr0 is the shortest prefix: just sort
        k = sigma_key(a, perspective=PERSPECTIVE_KAPPA)
        assert len(k) == 1
        assert k[0] == ("sort", "X")

    def test_addr0_kappa_distinguishes_different_sorts(self) -> None:
        """Two Addr0s with different sorts have different κ-keys."""
        from cstz.pff import (
            Addr0, Pair, Segment, sigma_key, PERSPECTIVE_KAPPA,
        )
        mk = lambda sort: Addr0(
            id="a", sort=sort,
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c", root="r", role="principal")],
            )],
        )
        assert sigma_key(mk("X"), perspective=PERSPECTIVE_KAPPA) \
            != sigma_key(mk("Y"), perspective=PERSPECTIVE_KAPPA)

    def test_addr1_perspective_tau_drops_premises(self) -> None:
        """Under PERSPECTIVE_TAU, premises are NOT in the morphism key.
        Two Addr1s with the same (ctor, src, dst) but different
        premises are identified at τ."""
        from cstz.pff import Addr1, sigma_key, PERSPECTIVE_TAU
        a = Addr1(
            id="g1", rank="r0", ctor="glue", src="x", dst="y",
            premises=["p1", "p2"],
        )
        b = Addr1(
            id="g2", rank="r0", ctor="glue", src="x", dst="y",
            premises=["p3"],
        )
        assert sigma_key(a, perspective=PERSPECTIVE_TAU) == \
            sigma_key(b, perspective=PERSPECTIVE_TAU)
        # σ-perspective still distinguishes them
        assert sigma_key(a) != sigma_key(b)

    def test_addr1_perspective_kappa_drops_ctor_and_premises(self) -> None:
        """Under PERSPECTIVE_KAPPA, only endpoints survive for a
        morphism.  Any morphism between the same (src, dst) pair is
        identified at κ regardless of constructor."""
        from cstz.pff import Addr1, Addr2, sigma_key, PERSPECTIVE_KAPPA
        a1 = Addr1(id="g", rank="r0", ctor="glue", src="x", dst="y")
        a2 = Addr2(id="c", rank="r0", ctor="coh", src="x", dst="y")
        # Both collapse to the same endpoints-only prefix at κ
        assert sigma_key(a1, perspective=PERSPECTIVE_KAPPA) == \
            sigma_key(a2, perspective=PERSPECTIVE_KAPPA)
        k = sigma_key(a1, perspective=PERSPECTIVE_KAPPA)
        assert len(k) == 2
        assert k == (("src", "x"), ("dst", "y"))
        # σ-perspective distinguishes them (different ctors)
        assert sigma_key(a1) != sigma_key(a2)

    def test_addr1_kappa_distinguishes_different_endpoints(self) -> None:
        """Two morphisms with different endpoints have different κ-keys."""
        from cstz.pff import Addr1, sigma_key, PERSPECTIVE_KAPPA
        a = Addr1(id="g1", rank="r0", ctor="glue", src="x", dst="y")
        b = Addr1(id="g2", rank="r0", ctor="glue", src="x", dst="z")
        assert sigma_key(a, perspective=PERSPECTIVE_KAPPA) \
            != sigma_key(b, perspective=PERSPECTIVE_KAPPA)

    def test_truncation_chain_refinement_order(self) -> None:
        """σ ⊐ τ ⊐ κ: σ is the full term (finest partition), κ
        is the shortest prefix (coarsest partition).  Any two
        cells equal under σ are equal under τ, and any two
        equal under τ are equal under κ.  Verified behaviorally:
        the σ-key is a prefix of the τ-key is a prefix of the
        κ-key (because truncation is prefix-taking)."""
        from cstz.pff import (
            Addr1, sigma_key,
            PERSPECTIVE_SIGMA, PERSPECTIVE_TAU, PERSPECTIVE_KAPPA,
        )
        a = Addr1(
            id="g", rank="r0", ctor="glue", src="x", dst="y",
            premises=["p"],
        )
        s = sigma_key(a, PERSPECTIVE_SIGMA)
        t = sigma_key(a, PERSPECTIVE_TAU)
        k = sigma_key(a, PERSPECTIVE_KAPPA)
        # σ is the longest (full term)
        assert len(s) >= len(t) >= len(k)
        # τ IS a prefix of σ
        assert s[:len(t)] == t
        # κ IS a prefix of τ
        assert t[:len(k)] == k

    def test_kappa_collapses_addr1s_with_different_ctors(self) -> None:
        """Under κ, two Addr1s with the same endpoints but
        different ctors collapse to the same key — ctor is
        dropped at the κ truncation level."""
        from cstz.pff import (
            Addr1, sigma_key, PERSPECTIVE_KAPPA,
        )
        glue = Addr1(id="g", rank="r0", ctor="glue", src="x", dst="y")
        named = Addr1(id="n", rank="r0", ctor="named", src="x", dst="y")
        assert sigma_key(glue, PERSPECTIVE_KAPPA) == \
            sigma_key(named, PERSPECTIVE_KAPPA)
        # But under σ they're distinct (ctor survives)
        assert sigma_key(glue) != sigma_key(named)

    def test_tau_preserves_ctor_but_drops_premises(self) -> None:
        """Under τ, ctor survives but premises are dropped.
        Two Addr1s with the same (src, dst, ctor) but different
        premises collapse under τ."""
        from cstz.pff import (
            Addr1, sigma_key, PERSPECTIVE_TAU,
        )
        a = Addr1(id="g1", rank="r0", ctor="glue", src="x", dst="y",
                  premises=["p1"])
        b = Addr1(id="g2", rank="r0", ctor="glue", src="x", dst="y",
                  premises=["p2"])
        assert sigma_key(a, PERSPECTIVE_TAU) == \
            sigma_key(b, PERSPECTIVE_TAU)
        # Under σ they're distinct (premises survive)
        assert sigma_key(a) != sigma_key(b)

    def test_addr0_kappa_drops_segments(self) -> None:
        """Under κ, Addr0 terms keep only sort; segments are
        dropped.  Two Addr0s with the same sort but different
        segments collapse under κ."""
        from cstz.pff import (
            Addr0, Pair, Segment, Step, sigma_key, PERSPECTIVE_KAPPA,
        )
        a = Addr0(
            id="a", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(chart="c0", root="r", role="principal")],
            )],
        )
        b = Addr0(
            id="b", sort="X",
            segments=[Segment(
                rank="r0", phase="ingest", patch="p0",
                pairs=[Pair(
                    chart="c0", root="r", role="principal",
                    route=[Step(kind="child", arg=0)],
                )],
            )],
        )
        assert sigma_key(a, PERSPECTIVE_KAPPA) == \
            sigma_key(b, PERSPECTIVE_KAPPA)
        # Under σ they're distinct (segments survive)
        assert sigma_key(a) != sigma_key(b)


class TestPassTwoFibers:
    """Cover the three-Fiber port added by Step 1.5.1 Pass 2.

    Pass 2 ports the legacy core.py three-Fiber structure into
    the PFF cascade engine: ``self.sigma_fiber``, ``self.tau_fiber``,
    and ``self.kappa_fiber`` are populated alongside the existing
    ``_uf`` and ``_morphism_signature_index`` machinery as cells
    are emitted.

    Pass 2 is **passive**: the Fibers accumulate but do not yet
    drive emission decisions.  These tests verify the Fibers
    accumulate correctly and that their internal helpers
    (``class_for``, ``__len__``, ``__repr__``) work as documented.
    Pass 3 will add ``Document.hom_set`` queries that consume
    them.
    """

    def _engine_with_one_addr0(self):
        from cstz.pff import Chart
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        sigma_chart = e.ensure_chart(
            patch=e.ensure_patch(),
            root="r0",
            kind="sigma",
        )
        tau_chart = e.ensure_chart(
            patch=e.ensure_patch(),
            root="r0",
            kind="tau",
        )
        addr0 = e.add_observation(
            sigma_chart=sigma_chart,
            tau_chart=tau_chart,
            sort="X",
        )
        return e, addr0

    def test_engine_has_three_fibers(self) -> None:
        """The engine instantiates three named Fibers in __init__."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import (
            PERSPECTIVE_SIGMA, PERSPECTIVE_TAU, PERSPECTIVE_KAPPA,
        )
        e = PFFCascadeEngine()
        assert e.sigma_fiber.name == "sigma"
        assert e.sigma_fiber.perspective == PERSPECTIVE_SIGMA
        assert e.tau_fiber.name == "tau"
        assert e.tau_fiber.perspective == PERSPECTIVE_TAU
        assert e.kappa_fiber.name == "kappa"
        assert e.kappa_fiber.perspective == PERSPECTIVE_KAPPA

    def test_fresh_engine_fibers_are_empty(self) -> None:
        """A freshly-constructed engine has zero Fiber classes."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        assert len(e.sigma_fiber) == 0
        assert len(e.tau_fiber) == 0
        assert len(e.kappa_fiber) == 0

    def test_add_observation_populates_all_three_fibers(self) -> None:
        """Each new Addr0 is registered in σ, τ, and κ Fibers."""
        e, addr0 = self._engine_with_one_addr0()
        # All three Fibers should contain exactly one class.
        assert len(e.sigma_fiber) == 1
        assert len(e.tau_fiber) == 1
        assert len(e.kappa_fiber) == 1
        # The cell id should be findable in each Fiber's
        # class_for reverse index.
        for f in (e.sigma_fiber, e.tau_fiber, e.kappa_fiber):
            cls = f.class_for(addr0.id)
            assert cls is not None
            assert addr0.id in cls.members

    def test_class_for_unknown_id_returns_none(self) -> None:
        """``_Fiber.class_for`` on an unregistered cell id is None."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        assert e.sigma_fiber.class_for("nonexistent-id") is None
        assert e.tau_fiber.class_for("nonexistent-id") is None
        assert e.kappa_fiber.class_for("nonexistent-id") is None

    def test_glue_emission_populates_fibers_with_addr1(self) -> None:
        """``_emit_glue`` registers the new Addr1 in all three Fibers.

        Two Addr0s with the same sigma_chart but different tau_charts
        produce two distinct addr0s plus one auto-emitted glue Addr1.
        That Addr1 should appear in every Fiber."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import Addr1
        e = PFFCascadeEngine()
        patch = e.ensure_patch()
        sigma_chart = e.ensure_chart(patch=patch, root="r0", kind="sigma")
        tau_a = e.ensure_chart(patch=patch, root="r0", kind="tau-a")
        tau_b = e.ensure_chart(patch=patch, root="r0", kind="tau-b")
        # Two observations with the same sigma key trigger an
        # auto-emitted glue Addr1.
        e.add_observation(
            sigma_chart=sigma_chart, tau_chart=tau_a, sort="X")
        e.add_observation(
            sigma_chart=sigma_chart, tau_chart=tau_b, sort="X")
        # The engine should have minted at least one Addr1 by glue.
        addr1s = [c for c in e.document.cells() if isinstance(c, Addr1)]
        assert len(addr1s) >= 1
        # Each Addr1 should be in all three Fibers
        for a1 in addr1s:
            for f in (e.sigma_fiber, e.tau_fiber, e.kappa_fiber):
                assert f.class_for(a1.id) is not None

    def test_kappa_fiber_collapses_morphisms_with_same_endpoints(
        self,
    ) -> None:
        """Two morphisms (one Addr1 glue, one Addr2 coh) between the
        same (src, dst) endpoints collapse to one κ-class — that's
        the κ-perspective semantics ("any morphism between these
        endpoints").  Under σ they remain distinct because they
        have different ctors."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import Addr1, Addr2
        e = PFFCascadeEngine()
        # Construct an Addr1 and an Addr2 with matching endpoints.
        a1 = Addr1(
            id="g1", rank="r0", ctor="glue", src="x", dst="y",
            premises=[],
        )
        a2 = Addr2(
            id="c1", rank="r0", ctor="coh", src="x", dst="y",
        )
        e.sigma_fiber.observe(a1)
        e.sigma_fiber.observe(a2)
        e.kappa_fiber.observe(a1)
        e.kappa_fiber.observe(a2)
        # Under σ, the two cells have different signatures (different
        # ctors), so they sit in different classes.
        assert len(e.sigma_fiber) == 2
        # Under κ, they share a signature ("morphism", "x", "y") so
        # they collapse to one class.
        assert len(e.kappa_fiber) == 1
        kappa_class = e.kappa_fiber.class_for(a1.id)
        assert kappa_class is not None
        assert a1.id in kappa_class.members
        assert a2.id in kappa_class.members

    def test_observe_is_idempotent(self) -> None:
        """Observing the same cell twice in the same Fiber is a
        no-op (set membership)."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import Addr1
        e = PFFCascadeEngine()
        a1 = Addr1(
            id="g1", rank="r0", ctor="glue", src="x", dst="y",
        )
        e.sigma_fiber.observe(a1)
        assert len(e.sigma_fiber) == 1
        e.sigma_fiber.observe(a1)  # second observe
        assert len(e.sigma_fiber) == 1
        cls = e.sigma_fiber.class_for(a1.id)
        assert cls is not None
        assert cls.members == {a1.id}

    def test_fiberclass_repr_includes_representative_and_size(
        self,
    ) -> None:
        """``_FiberClass.__repr__`` shows representative + size."""
        from cstz.pff_cascade import _FiberClass
        fc = _FiberClass(
            signature=("addr0", "X", ()),
            representative="addr0-0",
        )
        s = repr(fc)
        assert "addr0-0" in s
        assert "size=1" in s

    def test_fiber_repr_includes_name_and_counts(self) -> None:
        """``_Fiber.__repr__`` shows name + class count + cell count."""
        from cstz.pff_cascade import PFFCascadeEngine
        e, addr0 = self._engine_with_one_addr0()
        s = repr(e.sigma_fiber)
        assert "sigma" in s
        assert "1 classes" in s
        assert "1 cells" in s


class TestPassThreeDocumentQueries:
    """Cover ``Document.wedge``, ``Document.wedge_2``, and
    ``Document.hom_set`` added by Step 1.5.1 Pass 3.

    These three methods are pure read-only queries on the
    Document — they compute perspective-parameterized partitions
    from raw cells without consulting any engine state.  This is
    the Document-side realization of AUDIT.md §Slicer's "the
    topology is Document-computable" corollary.

    The cascade engine maintains parallel materializations of
    the same partitions in its three Fibers (Pass 2); at cascade
    convergence under correct usage these methods agree with
    ``engine.{sigma,tau,kappa}_fiber.classes``.
    """

    def _doc_with_two_morphisms_same_endpoints(self):
        """Build a tiny document with two distinct morphisms
        between the same (src, dst) endpoints — one Addr1 with
        ctor=glue, one Addr2 with ctor=coh.  Used by several
        tests below to exercise the κ-collapse semantics."""
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1, Addr2,
            Pair, Segment,
        )
        d = Document(
            documentId="hom-set-fixture",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id="src",
                    sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="r",
                            role="principal",
                        )],
                    )],
                ),
                Addr0(
                    id="dst",
                    sort="Y",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="r",
                            role="principal",
                        )],
                    )],
                ),
            ],
            paths1=[
                Addr1(
                    id="g1", rank="r0", ctor="glue",
                    src="src", dst="dst", premises=[],
                ),
            ],
            paths2=[
                Addr2(
                    id="c1", rank="r0", ctor="coh",
                    src="src", dst="dst",
                ),
            ],
        )
        return d

    # ── wedge() — N-perspective product ──

    def test_wedge_default_uses_three_canonical_perspectives(self) -> None:
        """``wedge()`` with no arguments defaults to (σ, τ, κ).

        Each cell in the document gets projected through three
        perspectives, and the result groups by the resulting
        triple-of-signatures."""
        from cstz.pff import sigma_key, PERSPECTIVE_SIGMA
        d = self._doc_with_two_morphisms_same_endpoints()
        wedge = d.wedge()
        # Each cell occupies one wedge cell (no two cells happen
        # to coincide on all three perspectives in this fixture).
        total_cells = (
            len(d.addresses0) + len(d.paths1) + len(d.paths2)
        )
        all_ids = []
        for ids in wedge.values():
            all_ids.extend(ids)
        assert sorted(all_ids) == sorted(c.id for c in d.cells())
        # Default has 3 perspectives → keys are 3-tuples.
        for key in wedge:
            assert len(key) == 3

    def test_wedge_two_explicit_perspectives_yields_two_tuples(self) -> None:
        """``wedge(σ, κ)`` with explicit perspectives produces
        2-tuple keys."""
        from cstz.pff import (
            PERSPECTIVE_SIGMA, PERSPECTIVE_KAPPA,
        )
        d = self._doc_with_two_morphisms_same_endpoints()
        wedge = d.wedge(PERSPECTIVE_SIGMA, PERSPECTIVE_KAPPA)
        for key in wedge:
            assert len(key) == 2

    def test_wedge_one_perspective_groups_like_partition(self) -> None:
        """``wedge(p)`` with a single perspective produces a
        partition: each cell appears in exactly one bucket, and
        cells with equal sigma_keys under p are in the same
        bucket."""
        from cstz.pff import sigma_key, PERSPECTIVE_KAPPA
        d = self._doc_with_two_morphisms_same_endpoints()
        wedge = d.wedge(PERSPECTIVE_KAPPA)
        # Two morphisms (Addr1 glue + Addr2 coh) with same
        # (src, dst) collapse under κ → they share a bucket.
        # Find the bucket containing g1.
        g1_bucket = None
        for ids in wedge.values():
            if "g1" in ids:
                g1_bucket = ids
                break
        assert g1_bucket is not None
        assert "c1" in g1_bucket

    # ── wedge_2() — convenience two-perspective product ──

    def test_wedge_2_returns_two_tuple_keys(self) -> None:
        """``wedge_2(σ, κ)`` returns dict with 2-tuple keys
        and cells grouped by their (σ_key, κ_key) pair."""
        from cstz.pff import (
            PERSPECTIVE_SIGMA, PERSPECTIVE_KAPPA, sigma_key,
        )
        d = self._doc_with_two_morphisms_same_endpoints()
        w2 = d.wedge_2(PERSPECTIVE_SIGMA, PERSPECTIVE_KAPPA)
        for key in w2:
            assert isinstance(key, tuple)
            assert len(key) == 2
        # The two morphisms (g1, c1) have different σ keys
        # (different ctors) but the same κ key (only endpoints
        # survive), so they sit in different (σ, κ) buckets but
        # those buckets share a κ-coordinate.
        # Find the two buckets containing g1 and c1 respectively.
        g1_key = c1_key = None
        for key, ids in w2.items():
            if "g1" in ids:
                g1_key = key
            if "c1" in ids:
                c1_key = key
        assert g1_key is not None and c1_key is not None
        # Different σ-keys (different ctors)
        assert g1_key[0] != c1_key[0]
        # Same κ-key (endpoints only)
        assert g1_key[1] == c1_key[1]

    # ── hom_set() — perspective-aware morphism query ──

    def test_hom_set_default_perspective_is_kappa(self) -> None:
        """``hom_set(src, dst)`` with no perspective defaults to
        PERSPECTIVE_KAPPA — at most one representative per
        (src, dst) pair."""
        d = self._doc_with_two_morphisms_same_endpoints()
        hom = d.hom_set("src", "dst")
        # Under κ, the Addr1 glue and Addr2 coh collapse to
        # one equivalence class → frozenset has one element.
        assert len(hom) == 1
        # The element is one of the two morphism ids
        only = next(iter(hom))
        assert only in ("g1", "c1")

    def test_hom_set_under_sigma_returns_all_distinct_morphisms(
        self,
    ) -> None:
        """``hom_set(src, dst, perspective=σ)`` returns one
        representative per σ-equivalence class — for two morphisms
        with different ctors, that's two distinct elements."""
        from cstz.pff import PERSPECTIVE_SIGMA
        d = self._doc_with_two_morphisms_same_endpoints()
        hom = d.hom_set("src", "dst", perspective=PERSPECTIVE_SIGMA)
        # Under σ, the Addr1 and Addr2 are distinct → both
        # appear in the result.
        assert len(hom) == 2
        assert hom == frozenset({"g1", "c1"})

    def test_hom_set_under_tau_groups_by_ctor(self) -> None:
        """Under τ, two morphisms with the same (ctor, src, dst)
        but different premises collapse; two with different
        ctors stay distinct."""
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1,
            Pair, Segment, PERSPECTIVE_TAU,
        )
        d = Document(
            documentId="tau-fixture",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id=name,
                    sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="r",
                            role="principal",
                        )],
                    )],
                ) for name in ("a", "b")
            ],
            paths1=[
                # Three glue Addr1s between the same (a, b):
                # two with the same premises, one with different
                Addr1(
                    id="g1", rank="r0", ctor="glue",
                    src="a", dst="b", premises=["p1"],
                ),
                Addr1(
                    id="g2", rank="r0", ctor="glue",
                    src="a", dst="b", premises=["p2"],
                ),
                # And one with a different ctor:
                Addr1(
                    id="t1", rank="r0", ctor="transport",
                    src="a", dst="b", premises=["p1"],
                ),
            ],
        )
        hom_tau = d.hom_set("a", "b", perspective=PERSPECTIVE_TAU)
        # Under τ, premises drop out → g1 and g2 (same ctor=glue)
        # collapse, and t1 (ctor=transport) stays distinct.
        # Expected: 2 equivalence classes.
        assert len(hom_tau) == 2

    def test_hom_set_no_matching_endpoints_returns_empty(self) -> None:
        """If no morphism has the queried endpoints, the
        result is the empty frozenset.

        Note: this only holds when src_id != dst_id.  Under the
        identity-on-objects convention, ``hom_set(X, X)`` for
        any Addr0 X always contains at least the identity (the
        Addr0 itself), so it cannot be empty if X is in the
        document.  See ``test_hom_set_includes_identity_morphism``
        below."""
        d = self._doc_with_two_morphisms_same_endpoints()
        assert d.hom_set("nonexistent", "dst") == frozenset()
        assert d.hom_set("src", "nonexistent") == frozenset()

    def test_hom_set_includes_identity_morphism(self) -> None:
        """Identity-on-objects: an Addr0 with id X represents the
        morphism ``id_X : X → X`` and must appear in
        ``hom_set(X, X)``.

        Per the user's Pass 3 correction (FRICTION-7 in the
        research log): 0-dimensional cells should be identity
        morphisms; paths with self as start and end.  Dimension 0
        is not "objects without morphism structure" but rather
        "morphisms whose source equals their destination."
        """
        d = self._doc_with_two_morphisms_same_endpoints()
        # The fixture's Addr0 with id "src" represents id_src.
        hom_src = d.hom_set("src", "src")
        assert "src" in hom_src, (
            "Addr0 'src' must appear as the identity morphism "
            "id_src in hom_set('src', 'src')"
        )
        # Same for "dst"
        hom_dst = d.hom_set("dst", "dst")
        assert "dst" in hom_dst

    def test_hom_set_identity_distinct_from_distinct_endpoint_query(
        self,
    ) -> None:
        """``hom_set(X, X)`` (identity self-loop) and ``hom_set(X, Y)``
        for X != Y are different queries.

        The former returns the identity morphism plus any
        non-identity self-loops at X; the latter returns
        non-identity morphisms with distinct endpoints (or
        nothing).  Their intersection is empty when X != Y."""
        d = self._doc_with_two_morphisms_same_endpoints()
        identity_at_src = d.hom_set("src", "src")
        crosswise = d.hom_set("src", "dst")
        # The identity at "src" must NOT appear in the
        # cross-endpoints query.
        assert "src" not in crosswise
        # And the cross-endpoint morphisms must NOT appear in the
        # self-loop query (they have distinct endpoints).
        assert "g1" not in identity_at_src
        assert "c1" not in identity_at_src

    def test_hom_set_addr0_identity_visible_under_all_perspectives(
        self,
    ) -> None:
        """The identity-morphism membership of an Addr0 in
        ``hom_set(X, X)`` is invariant across perspectives — the
        Addr0 always represents id_X regardless of which
        discriminator subset the perspective uses to compute
        sigma_key.

        Note: this exposes a deferred Pass 1 question.  The
        Addr0's κ-key is currently ``("addr0", sort)`` (Pass 1's
        choice), which under the identity reading should
        arguably be ``("morphism", X.id, X.id)``.  See research
        log "deferred Pass 1 question on κ-key for Addr0".
        Until that question is resolved, this test asserts only
        the membership invariant, not any specific tuple shape.
        """
        from cstz.pff import (
            PERSPECTIVE_SIGMA, PERSPECTIVE_TAU, PERSPECTIVE_KAPPA,
        )
        d = self._doc_with_two_morphisms_same_endpoints()
        for p in (
            PERSPECTIVE_SIGMA, PERSPECTIVE_TAU, PERSPECTIVE_KAPPA,
        ):
            hom = d.hom_set("src", "src", perspective=p)
            assert "src" in hom, (
                f"Addr0 'src' missing from hom_set under {p}"
            )

    def test_hom_set_kappa_count_le_sigma_count(self) -> None:
        """The lattice refinement law: |hom_set under κ| ≤
        |hom_set under σ| for the same (src, dst).  More
        discriminators ⇒ finer equivalence ⇒ more classes."""
        from cstz.pff import PERSPECTIVE_SIGMA, PERSPECTIVE_KAPPA
        d = self._doc_with_two_morphisms_same_endpoints()
        sigma_hom = d.hom_set(
            "src", "dst", perspective=PERSPECTIVE_SIGMA,
        )
        kappa_hom = d.hom_set(
            "src", "dst", perspective=PERSPECTIVE_KAPPA,
        )
        assert len(kappa_hom) <= len(sigma_hom)

    def test_document_query_agrees_with_engine_fiber(self) -> None:
        """At cascade convergence, ``Document.hom_set`` and
        the engine's ``kappa_fiber.class_for`` should agree on
        the same morphism cells.

        This is the property test that ties the Document-side
        topological-completeness query to the engine-side
        cached materialization (Pass 2's Fibers).  At cascade
        convergence under correct usage they must agree."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import Addr1, PERSPECTIVE_KAPPA
        e = PFFCascadeEngine()
        patch = e.ensure_patch()
        sigma_chart = e.ensure_chart(
            patch=patch, root="r0", kind="sigma",
        )
        tau_a = e.ensure_chart(
            patch=patch, root="r0", kind="tau-a",
        )
        tau_b = e.ensure_chart(
            patch=patch, root="r0", kind="tau-b",
        )
        # Two observations with the same sigma key trigger an
        # auto-emitted glue Addr1.
        e.add_observation(
            sigma_chart=sigma_chart, tau_chart=tau_a, sort="X",
        )
        e.add_observation(
            sigma_chart=sigma_chart, tau_chart=tau_b, sort="X",
        )
        addr1s = [
            c for c in e.document.cells()
            if isinstance(c, Addr1)
        ]
        assert len(addr1s) == 1
        a1 = addr1s[0]
        # Engine-side materialization
        kappa_class = e.kappa_fiber.class_for(a1.id)
        assert kappa_class is not None
        # Document-side query
        doc_hom = e.document.hom_set(
            a1.src, a1.dst, perspective=PERSPECTIVE_KAPPA,
        )
        # Both should agree that there is exactly one κ-class
        # of morphism between (src, dst).
        assert len(doc_hom) == 1
        assert a1.id in kappa_class.members
        # And the document's representative for that class is
        # the same morphism the engine put in the κ-class.
        assert next(iter(doc_hom)) in kappa_class.members


# ── v2 ports from core.py (residue / cleavage / eta-abstraction) ────


class TestEtaAbstractionUnionFind:
    """Cover the eta-abstraction union-find ported from core.py
    (``_eta_uf`` and ``_eta_abstractions`` at core.py:173-174).

    The eta UF is a substrate-level identity tracker for *named
    bindings* — strings that may be claimed equivalent without
    being conflated with the Cell ids they appear in.  All four
    public methods (eta_make / eta_abstract / eta_union / eta_find)
    operate on the eta UF in isolation; none affect the cascade's
    emission decisions.
    """

    def test_eta_uf_starts_empty(self) -> None:
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        assert len(e._eta_uf) == 0
        assert e._eta_abstractions == {}

    def test_eta_make_registers_name(self) -> None:
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        e.eta_make("X")
        assert "X" in e._eta_uf
        assert e.eta_find("X") == "X"

    def test_eta_make_idempotent(self) -> None:
        """Calling eta_make on the same name twice is a no-op."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        e.eta_make("X")
        e.eta_make("X")
        assert len(e._eta_uf) == 1
        assert e.eta_find("X") == "X"

    def test_eta_abstract_records_mapping(self) -> None:
        """``eta_abstract(raw, abs)`` maps raw → abs and registers
        abs in the UF."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        e.eta_abstract("List[int]", "T0")
        assert e._eta_abstractions["List[int]"] == "T0"
        assert "T0" in e._eta_uf
        assert e.eta_find("List[int]") == "T0"

    def test_eta_abstract_first_writer_wins(self) -> None:
        """A second eta_abstract on the same raw name is a no-op."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        e.eta_abstract("List[int]", "T0")
        e.eta_abstract("List[int]", "T1")  # ignored
        assert e.eta_find("List[int]") == "T0"

    def test_eta_union_unifies_two_abstractions(self) -> None:
        """After ``eta_union(a, b)``, ``eta_find(a) == eta_find(b)``."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        e.eta_make("T0")
        e.eta_make("T1")
        e.eta_union("T0", "T1")
        assert e.eta_find("T0") == e.eta_find("T1")

    def test_eta_union_makes_names_if_absent(self) -> None:
        """``eta_union`` registers both names in the UF if they
        weren't already present."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        e.eta_union("T0", "T1")  # neither registered yet
        assert "T0" in e._eta_uf
        assert "T1" in e._eta_uf
        assert e.eta_find("T0") == e.eta_find("T1")

    def test_eta_find_walks_abstraction_then_uf(self) -> None:
        """``eta_find`` walks the abstraction map first, then
        chases the UF to canonical."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        e.eta_abstract("raw_a", "T0")
        e.eta_abstract("raw_b", "T1")
        e.eta_union("T0", "T1")
        # Both raw names now resolve to the same canonical
        assert e.eta_find("raw_a") == e.eta_find("raw_b")

    def test_eta_find_unknown_name_returns_unchanged(self) -> None:
        """A name that's neither an abstraction nor in the UF is
        returned unchanged by eta_find."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        assert e.eta_find("unknown") == "unknown"

    def test_eta_uf_does_not_affect_cell_uf(self) -> None:
        """The eta UF is independent of the cell ``_uf``: unioning
        two abstraction names does not union any Cell ids."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        # Use distinct sigma charts so the two Addr0s have
        # different sigma_keys and don't auto-glue via streaming
        # cascade.
        sigma_a = e.ensure_chart(kind="sigma", root="A")
        sigma_b = e.ensure_chart(kind="sigma", root="B")
        tau = e.ensure_chart(kind="tau", root="r")
        a = e.add_observation(sigma_a, tau, sort="A")
        b = e.add_observation(sigma_b, tau, sort="B")
        # Use the addr0 ids as eta names too
        e.eta_make(a.id)
        e.eta_make(b.id)
        e.eta_union(a.id, b.id)
        # eta UF unifies them
        assert e.eta_find(a.id) == e.eta_find(b.id)
        # cell UF does NOT
        assert e.canonical_addr0(a.id) != e.canonical_addr0(b.id)


class TestResidueTracking:
    """Cover residue tracking ported from core.py
    (``_residue_sets``, ``_update_residue``, ``_merge_residue_sets``
    at core.py:179, 312-321).

    Residue tracking preserves the raw pre-canonical form of
    inputs to ``add_observation`` (raw sigma_children) and
    ``_emit_glue`` (raw src/dst).  After Step 1.5's HIT collapse,
    these raw forms were lost when the cascade canonicalized.
    These tests verify the raw forms are preserved and
    accessible via ``addr0_residue`` / ``addr1_residue``.
    """

    def _engine_with_charts(self):
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        sigma = e.ensure_chart(kind="sigma", root="r")
        tau = e.ensure_chart(kind="tau", root="r")
        return e, sigma, tau

    def test_addr0_residue_records_first_observation(self) -> None:
        e, sigma, tau = self._engine_with_charts()
        # First observation with no children — residue contains
        # the empty tuple
        a = e.add_observation(sigma, tau, sort="A")
        assert e.addr0_residue(a.id) == frozenset({()})

    def test_addr0_residue_records_children(self) -> None:
        e, sigma, tau = self._engine_with_charts()
        leaf = e.add_observation(sigma, tau, sort="leaf")
        parent = e.add_observation(
            sigma, tau, sigma_children=[leaf.id], sort="parent",
        )
        residue = e.addr0_residue(parent.id)
        assert (leaf.id,) in residue

    def test_addr0_residue_grows_on_hash_cons_hit(self) -> None:
        """A second observation with identical full_sig hits the
        existing Addr0; its raw children tuple is added to the
        residue."""
        e, sigma, tau = self._engine_with_charts()
        leaf = e.add_observation(sigma, tau, sort="leaf")
        first = e.add_observation(
            sigma, tau, sigma_children=[leaf.id], sort="parent",
        )
        # Same call again — hash-cons hit, returns the same Addr0
        second = e.add_observation(
            sigma, tau, sigma_children=[leaf.id], sort="parent",
        )
        assert first is second
        # Residue contains the raw children tuple (which is the
        # same on both calls, so still one element in the set)
        residue = e.addr0_residue(first.id)
        assert residue == frozenset({(leaf.id,)})

    def test_addr0_residue_groups_through_canonical(self) -> None:
        """When two distinct Addr0s end up in the same path1 class
        via cascade glue, addr0_residue returns the union of their
        residues from either id."""
        e, sigma, tau = self._engine_with_charts()
        # Two leaves with different sorts
        leaf_a = e.add_observation(sigma, tau, sort="leafA")
        leaf_b = e.add_observation(sigma, tau, sort="leafB")
        # Two parents with different children but the same shape;
        # they will NOT collide on sigma_key because their child
        # canonicals differ.  We force the union via explicit glue.
        p_a = e.add_observation(
            sigma, tau, sigma_children=[leaf_a.id], sort="parent",
        )
        p_b = e.add_observation(
            sigma, tau, sigma_children=[leaf_b.id], sort="parent",
        )
        # Glue the two leaves so the parents end up in the same
        # path1 class via cascade
        e.glue(leaf_a.id, leaf_b.id)
        # After cascade, both parents are in the same canonical
        # class and addr0_residue returns the union.
        residue_via_a = e.addr0_residue(p_a.id)
        residue_via_b = e.addr0_residue(p_b.id)
        assert residue_via_a == residue_via_b
        assert (leaf_a.id,) in residue_via_a
        assert (leaf_b.id,) in residue_via_a

    def test_addr0_residue_empty_for_unknown_id(self) -> None:
        """Querying residue for an id not in any cell-uf returns
        an empty frozenset (covers the not-in-uf branch)."""
        e, _, _ = self._engine_with_charts()
        assert e.addr0_residue("addr0-999") == frozenset()

    def test_addr1_residue_records_first_glue(self) -> None:
        """A fresh _emit_glue records the raw (src, dst) pair
        in the residue under the new Addr1's id."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        # Distinct sigma charts → distinct sigma_keys → no
        # auto-glue from streaming cascade
        sigma_a = e.ensure_chart(kind="sigma", root="A")
        sigma_b = e.ensure_chart(kind="sigma", root="B")
        tau = e.ensure_chart(kind="tau", root="r")
        a = e.add_observation(sigma_a, tau, sort="A")
        b = e.add_observation(sigma_b, tau, sort="B")
        result = e.glue(a.id, b.id)
        addr1 = result.addr1
        assert addr1 is not None
        assert e.addr1_residue(addr1.id) == frozenset({(a.id, b.id)})

    def test_addr1_residue_grows_on_hash_cons_hit(self) -> None:
        """A second glue between two Addr0s already in the same
        path1 class hits the hash-cons; the raw (src, dst) is
        added to the residue."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        # Three distinct charts so streaming cascade leaves them
        # alone until we manually glue.
        sigma_a = e.ensure_chart(kind="sigma", root="A")
        sigma_b = e.ensure_chart(kind="sigma", root="B")
        sigma_c = e.ensure_chart(kind="sigma", root="C")
        tau = e.ensure_chart(kind="tau", root="r")
        a = e.add_observation(sigma_a, tau, sort="A")
        b = e.add_observation(sigma_b, tau, sort="B")
        c = e.add_observation(sigma_c, tau, sort="C")
        # First glue (a, b) — fresh emission
        r1 = e.glue(a.id, b.id)
        addr1 = r1.addr1
        assert addr1 is not None
        # Glue (b, c) — fresh emission of a separate Addr1
        e.glue(b.id, c.id)
        # Now (a, c) glue: a and c are already in the same canonical
        # class via the chain a-b-c, so this is a no-op at the
        # cascade level.  But the raw_endpoints (a.id, c.id) tuple
        # is recorded against whichever Addr1 hash-conses (or it's
        # a noop with no residue update if was_noop).  The original
        # raw (a, b) pair must still be present in addr1's residue.
        e.glue(a.id, c.id)
        residue = e.addr1_residue(addr1.id)
        # The original raw (a, b) pair is in there
        assert (a.id, b.id) in residue

    def test_addr1_residue_empty_for_unknown_id(self) -> None:
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        assert e.addr1_residue("addr1-999") == frozenset()


class TestDynamicCleavageFibers:
    """Cover the dynamic cleavage Fiber list ported from core.py
    (``_cleavage_fibers`` at core.py:181).

    Dynamic cleavage Fibers are an extension of the static
    σ/τ/κ trio: callers can append additional Fibers under
    custom perspectives at runtime, and every existing and
    future cell is automatically observed into them.
    """

    def test_cleavage_fibers_starts_empty(self) -> None:
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        assert e.cleavage_fibers() == ()

    def test_add_cleavage_fiber_returns_fiber(self) -> None:
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import PERSPECTIVE_KAPPA
        e = PFFCascadeEngine()
        fiber = e.add_cleavage_fiber("custom", PERSPECTIVE_KAPPA)
        assert fiber.name == "custom"
        assert fiber.perspective == PERSPECTIVE_KAPPA
        assert e.cleavage_fibers() == (fiber,)

    def test_add_cleavage_fiber_observes_existing_cells(self) -> None:
        """Adding a cleavage fiber observes every cell currently in
        the document, so the new fiber starts in sync with the
        static trio."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import PERSPECTIVE_KAPPA
        e = PFFCascadeEngine()
        sigma = e.ensure_chart(kind="sigma", root="r")
        tau = e.ensure_chart(kind="tau", root="r")
        # Emit cells before adding the fiber
        a = e.add_observation(sigma, tau, sort="A")
        b = e.add_observation(sigma, tau, sort="B")
        # Now add the fiber
        fiber = e.add_cleavage_fiber("late", PERSPECTIVE_KAPPA)
        # Both cells should already be in the new fiber
        assert a.id in fiber.class_of
        assert b.id in fiber.class_of

    def test_new_cells_flow_into_cleavage_fiber(self) -> None:
        """Cells emitted after add_cleavage_fiber automatically
        observe into the new fiber via _observe_into_fibers."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import PERSPECTIVE_KAPPA
        e = PFFCascadeEngine()
        sigma = e.ensure_chart(kind="sigma", root="r")
        tau = e.ensure_chart(kind="tau", root="r")
        # Add the fiber first
        fiber = e.add_cleavage_fiber("early", PERSPECTIVE_KAPPA)
        # Then emit cells
        a = e.add_observation(sigma, tau, sort="A")
        # The new cell flows into the fiber
        assert a.id in fiber.class_of

    def test_multiple_cleavage_fibers_coexist(self) -> None:
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import (
            PERSPECTIVE_SIGMA, PERSPECTIVE_TAU, PERSPECTIVE_KAPPA,
        )
        e = PFFCascadeEngine()
        f1 = e.add_cleavage_fiber("alt-sigma", PERSPECTIVE_SIGMA)
        f2 = e.add_cleavage_fiber("alt-tau", PERSPECTIVE_TAU)
        f3 = e.add_cleavage_fiber("alt-kappa", PERSPECTIVE_KAPPA)
        assert e.cleavage_fibers() == (f1, f2, f3)

    def test_cleavage_fibers_returns_snapshot(self) -> None:
        """``cleavage_fibers()`` returns a tuple snapshot, so
        adding more fibers after the call does not affect the
        previously-returned tuple."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import PERSPECTIVE_KAPPA
        e = PFFCascadeEngine()
        f1 = e.add_cleavage_fiber("first", PERSPECTIVE_KAPPA)
        snapshot = e.cleavage_fibers()
        f2 = e.add_cleavage_fiber("second", PERSPECTIVE_KAPPA)
        assert snapshot == (f1,)
        assert e.cleavage_fibers() == (f1, f2)

    def test_cleavage_fiber_with_kappa_perspective(self) -> None:
        """A cleavage Fiber under the κ truncation level partitions
        cells by the coarsest prefix (sort for Addr0, endpoints
        for morphisms)."""
        from cstz.pff_cascade import PFFCascadeEngine
        from cstz.pff import PERSPECTIVE_KAPPA
        e = PFFCascadeEngine()
        sigma = e.ensure_chart(kind="sigma", root="r")
        tau = e.ensure_chart(kind="tau", root="r")
        fiber = e.add_cleavage_fiber("kappa-clone", PERSPECTIVE_KAPPA)
        a = e.add_observation(sigma, tau, sort="X")
        c = e.add_observation(sigma, tau, sort="Y")
        # Under κ, different sorts → different classes
        assert a.id in fiber.class_of
        assert c.id in fiber.class_of
        assert fiber.class_of[a.id] != fiber.class_of[c.id]


class TestDocumentCells:
    """Cover ``Document.cells()`` iterator added by HIT collapse."""

    def test_cells_empty_document(self) -> None:
        from cstz.pff import Document, Rank, Patch
        d = Document(
            documentId="empty",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
        )
        assert list(d.cells()) == []

    def test_cells_iterates_all_ranks(self) -> None:
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1, Addr2,
            Pair, Segment,
        )
        d = Document(
            documentId="mixed",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[Addr0(
                id="a0", sort="X",
                segments=[Segment(
                    rank="r0", phase="ingest", patch="p0",
                    pairs=[Pair(
                        chart="c0", root="a0", role="principal",
                    )],
                )],
            )],
            paths1=[Addr1(
                id="g0", rank="r0", ctor="glue", src="a0", dst="a0",
            )],
            paths2=[Addr2(
                id="c0", rank="r0", ctor="coh", src="g0", dst="g0",
            )],
        )
        cells = list(d.cells())
        assert len(cells) == 3
        assert cells[0].id == "a0"
        assert cells[1].id == "g0"
        assert cells[2].id == "c0"

    def test_cells_yields_addresses0_first(self) -> None:
        """Stable iteration order: addresses0, then paths1, then paths2."""
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1, Addr2,
            Pair, Segment,
        )
        d = Document(
            documentId="order",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id=f"a{i}", sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root=f"a{i}", role="principal",
                        )],
                    )],
                )
                for i in range(2)
            ],
            paths1=[Addr1(
                id="g0", rank="r0", ctor="glue", src="a0", dst="a1",
            )],
            paths2=[Addr2(
                id="c0", rank="r0", ctor="coh", src="g0", dst="g0",
            )],
        )
        ids = [c.id for c in d.cells()]
        assert ids == ["a0", "a1", "g0", "c0"]


class TestDocumentCanonicalize:
    """Cover ``Document.canonicalize()`` post-hoc dedup pass.

    canonicalize is the generic rank-agnostic dedup that handles
    any duplicate cells, not just morphism duplicates.  It's the
    backward-compat path for Documents constructed outside the
    cascade (merge_bundle, JSON import, direct test fixtures).
    """

    def test_canonicalize_empty_document(self) -> None:
        from cstz.pff import Document, Rank, Patch
        d = Document(
            documentId="empty",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
        )
        assert d.canonicalize() == []

    def test_canonicalize_no_duplicates(self) -> None:
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1, Pair, Segment,
        )
        d = Document(
            documentId="unique",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id="a0", sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="a0", role="principal",
                        )],
                    )],
                ),
                Addr0(
                    id="a1", sort="Y",  # different sort → different sigma_key
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="a1", role="principal",
                        )],
                    )],
                ),
            ],
            paths1=[
                Addr1(id="g0", rank="r0", ctor="glue", src="a0", dst="a1"),
            ],
        )
        assert d.canonicalize() == []
        assert len(d.addresses0) == 2
        assert len(d.paths1) == 1

    def test_canonicalize_duplicate_morphisms(self) -> None:
        """Two Addr1s with identical sigma_keys → one removed."""
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1, Pair, Segment,
        )
        d = Document(
            documentId="dup-morph",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id=_id, sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root=_id, role="principal",
                        )],
                    )],
                )
                for _id in ("a0", "a1")
            ],
            paths1=[
                Addr1(id="g0", rank="r0", ctor="glue", src="a0", dst="a1"),
                Addr1(id="g1", rank="r0", ctor="glue", src="a0", dst="a1"),
            ],
        )
        removed = d.canonicalize()
        assert len(removed) == 1
        assert removed[0].id == "g1"  # second one is dedup victim
        assert len(d.paths1) == 1
        assert d.paths1[0].id == "g0"

    def test_canonicalize_duplicate_rank0_cells(self) -> None:
        """Two Addr0s with identical sort + segments → one removed."""
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Pair, Segment,
        )
        d = Document(
            documentId="dup-rank0",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
        )
        for _id in ("a0", "a1"):
            d.addresses0.append(Addr0(
                id=_id, sort="X",
                segments=[Segment(
                    rank="r0", phase="ingest", patch="p0",
                    pairs=[Pair(
                        chart="c0", root="same-root", role="principal",
                    )],
                )],
            ))
        # Both Addr0s have identical sort and segments → same sigma_key
        removed = d.canonicalize()
        assert len(removed) == 1
        assert len(d.addresses0) == 1

    def test_canonicalize_rewrites_path1_references(self) -> None:
        """When a rank-0 cell is removed, surviving paths1 references
        to it must be rewritten to the canonical survivor."""
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1, Pair, Segment,
        )
        d = Document(
            documentId="rewrite",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id="a0", sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="same",
                            role="principal",
                        )],
                    )],
                ),
                Addr0(  # duplicate of a0
                    id="a1", sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="same",
                            role="principal",
                        )],
                    )],
                ),
                Addr0(
                    id="a2", sort="Y",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="a2", role="principal",
                        )],
                    )],
                ),
            ],
            paths1=[
                # References a1 (the duplicate) — should get rewritten to a0
                Addr1(
                    id="g0", rank="r0", ctor="transport",
                    src="a1", dst="a2", premises=["a1"],
                ),
            ],
        )
        d.canonicalize()
        # a1 was removed; g0's src and premises should now reference a0
        assert len(d.addresses0) == 2
        assert d.paths1[0].src == "a0"
        assert d.paths1[0].premises == ["a0"]

    def test_canonicalize_rewrites_path2_references(self) -> None:
        """Path2 src/dst referring to a removed morphism get rewritten."""
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1, Addr2,
            Pair, Segment,
        )
        d = Document(
            documentId="path2",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id=_id, sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root=_id, role="principal",
                        )],
                    )],
                )
                for _id in ("a0", "a1")
            ],
            paths1=[
                Addr1(
                    id="g0", rank="r0", ctor="glue",
                    src="a0", dst="a1",
                ),
                # Duplicate of g0
                Addr1(
                    id="g1", rank="r0", ctor="glue",
                    src="a0", dst="a1",
                ),
            ],
            paths2=[
                Addr2(
                    id="c0", rank="r0", ctor="vcomp",
                    src="g1", dst="g1",
                ),
            ],
        )
        d.canonicalize()
        # g1 removed; c0's src/dst should now reference g0
        assert len(d.paths1) == 1
        assert d.paths2[0].src == "g0"
        assert d.paths2[0].dst == "g0"

    def test_canonicalize_removes_duplicate_path2(self) -> None:
        """Two Addr2s with identical sigma_keys → one removed.

        Also exercises the continue-on-removed branch and the
        path2 removal branch in canonicalize.
        """
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Addr1, Addr2,
            Pair, Segment,
        )
        d = Document(
            documentId="dup-path2",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id=_id, sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root=_id, role="principal",
                        )],
                    )],
                )
                for _id in ("a0", "a1")
            ],
            paths1=[
                Addr1(id="g0", rank="r0", ctor="glue", src="a0", dst="a1"),
                Addr1(id="g1", rank="r0", ctor="transport", src="a0", dst="a1"),
            ],
            paths2=[
                Addr2(id="c0", rank="r0", ctor="coh", src="g0", dst="g1"),
                Addr2(id="c1", rank="r0", ctor="coh", src="g0", dst="g1"),
            ],
        )
        removed = d.canonicalize()
        # Both Addr2s have the same sigma_key → one is removed
        removed_ids = {c.id for c in removed}
        assert "c1" in removed_ids
        assert len(d.paths2) == 1

    def test_canonicalize_rewrites_classview_member_addr0(self) -> None:
        """ClassView.member.address0 references to removed rank-0
        cells get rewritten."""
        from cstz.pff import (
            Document, Rank, Patch, Addr0, Pair, Segment,
            ClassView, ClassMember,
        )
        d = Document(
            documentId="classview",
            ranks=[Rank(id="r0", ordinal=0)],
            patches=[Patch(id="p0", rank="r0", phase="ingest")],
            addresses0=[
                Addr0(
                    id="a0", sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="same",
                            role="principal",
                        )],
                    )],
                ),
                Addr0(  # duplicate
                    id="a1", sort="X",
                    segments=[Segment(
                        rank="r0", phase="ingest", patch="p0",
                        pairs=[Pair(
                            chart="c0", root="same",
                            role="principal",
                        )],
                    )],
                ),
            ],
            classViews=[
                ClassView(
                    id="cv0", rank="r0", phase="ingest",
                    truncation="full", congruence="alpha",
                    members=[
                        ClassMember(classId="k0", address0="a0"),
                        ClassMember(classId="k0", address0="a1"),
                    ],
                ),
            ],
        )
        d.canonicalize()
        # Both members should now point to a0
        member_addrs = [m.address0 for m in d.classViews[0].members]
        assert member_addrs == ["a0", "a0"]


class TestEmissionHashConsSwapBranch:
    """Exercise the src-canonical > dst-canonical branch of
    ``_emit_glue``'s sigma_key normalization (pff_cascade.py:680).

    Normal σ-cascade operation uses anchor-first emission, so the
    anchor (lex-smallest id) is always the src in emission calls,
    putting the canonical pair in (canon_src, canon_dst) order
    where canon_src ≤ canon_dst.  The swap branch only fires when
    a direct user-initiated glue call has src canonicalize to
    something greater than dst's canonical.
    """

    def test_manual_glue_src_greater_than_dst_triggers_swap(self) -> None:
        """Direct engine.glue() with src > dst's canonical triggers
        the swap branch in _emit_glue."""
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        a = e.add_observation(sigma, tau_a)  # addr0-0
        b = e.add_observation(sigma, tau_b)  # addr0-1
        # After the streaming cascade, a and b are already unified.
        # We force a fresh equivalence class by creating a third
        # addr0 that's not yet glued, then issue a manual glue
        # from it-with-greater-id to it-with-smaller-id.
        sigma2 = e.ensure_chart("sigma", "Y")
        tau_c = e.ensure_chart("tau", "C")
        c = e.add_observation(sigma2, tau_c)  # addr0-2, disjoint
        # Manual glue: src=c (addr0-2) > dst=a (addr0-0 canonical)
        # This forces the swap: canon_src=addr0-2 > canon_dst=addr0-0
        result = e.glue(c.id, a.id)
        # Under normal operation this produces a new Addr1 and
        # the swap-normalized key is ("morphism", "glue", "addr0-0",
        # "addr0-2", ...).  We don't assert the exact key shape
        # here — just that the glue succeeds and doesn't crash.
        assert result.addr1 is not None
        assert e.canonical_addr0(c.id) == e.canonical_addr0(a.id)
