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
