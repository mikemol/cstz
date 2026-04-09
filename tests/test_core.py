"""Tests for cstz.core — UnionFind, Fiber, FiberClass, SPPF."""
from __future__ import annotations

import pytest
from cstz.core import UnionFind, FiberClass, Fiber, SPPF


# ── UnionFind ────────────────────────────────────────────────────────

class TestUnionFind:
    def test_make_and_find(self) -> None:
        uf = UnionFind()
        uf.make(1)
        assert uf.find(1) == 1

    def test_make_idempotent(self) -> None:
        uf = UnionFind()
        uf.make(1)
        uf.make(1)  # should not reset
        assert uf.find(1) == 1

    def test_union_same(self) -> None:
        uf = UnionFind()
        uf.make(1)
        assert uf.union(1, 1) == 1

    def test_union_different(self) -> None:
        uf = UnionFind()
        uf.make(1)
        uf.make(2)
        rep = uf.union(1, 2)
        assert uf.find(1) == rep
        assert uf.find(2) == rep

    def test_union_rank_swap(self) -> None:
        """When rank[a] < rank[b], b becomes parent."""
        uf = UnionFind()
        uf.make(1)
        uf.make(2)
        uf.make(3)
        # union(1,2) → rank of winner becomes 1
        uf.union(1, 2)
        # union(3, winner) where 3 has rank 0 < 1
        rep = uf.union(3, uf.find(1))
        assert uf.find(3) == rep

    def test_union_equal_rank_increments(self) -> None:
        uf = UnionFind()
        uf.make(1)
        uf.make(2)
        # Both rank 0 → winner gets rank 1
        uf.union(1, 2)
        uf.make(3)
        uf.make(4)
        uf.union(3, 4)
        # Both rank 1 → winner gets rank 2
        uf.union(uf.find(1), uf.find(3))
        assert uf.find(1) == uf.find(3)

    def test_path_compression(self) -> None:
        uf = UnionFind()
        for i in range(5):
            uf.make(i)
        # Create chain: 0→1→2→3→4
        for i in range(4):
            uf._parent[i] = i + 1
        root = uf.find(0)
        assert root == 4
        # After compression, 0 points directly to 4
        assert uf._parent[0] == 4

    def test_contains(self) -> None:
        uf = UnionFind()
        assert 1 not in uf
        uf.make(1)
        assert 1 in uf

    def test_iter(self) -> None:
        uf = UnionFind()
        uf.make("a")
        uf.make("b")
        assert set(uf) == {"a", "b"}

    def test_len(self) -> None:
        uf = UnionFind()
        assert len(uf) == 0
        uf.make(1)
        assert len(uf) == 1

    def test_find_missing_raises(self) -> None:
        uf = UnionFind()
        with pytest.raises(KeyError):
            uf.find(999)


# ── FiberClass ───────────────────────────────────────────────────────

class TestFiberClass:
    def test_init_and_repr(self) -> None:
        fc = FiberClass(0, ("a",), (1, 2))
        assert fc.id == 0
        assert fc.signature == ("a",)
        assert fc.child_ids == (1, 2)
        assert fc.node_indices == []
        assert "FiberClass(0, 0 nodes)" in repr(fc)

    def test_repr_with_nodes(self) -> None:
        fc = FiberClass(5, ("x",), ())
        fc.node_indices = [0, 1, 2]
        assert "3 nodes" in repr(fc)


# ── Fiber ────────────────────────────────────────────────────────────

class TestFiber:
    def test_assign_new(self) -> None:
        f = Fiber("test")
        fid = f._assign(("sig",), (), 0)
        assert fid == 0
        assert f.classes[0].node_indices == [0]

    def test_assign_existing(self) -> None:
        f = Fiber("test")
        fid1 = f._assign(("sig",), (), 0)
        fid2 = f._assign(("sig",), (), 1)
        assert fid1 == fid2
        assert f.classes[fid1].node_indices == [0, 1]

    def test_canonical(self) -> None:
        f = Fiber("test")
        fid = f._assign(("a",), (), 0)
        assert f.canonical(fid) == fid

    def test_merge_same(self) -> None:
        f = Fiber("test")
        fid = f._assign(("a",), (), 0)
        assert f.merge(fid, fid) == fid

    def test_merge_different(self) -> None:
        f = Fiber("test")
        a = f._assign(("a",), (), 0)
        b = f._assign(("b",), (), 1)
        winner = f.merge(a, b)
        assert f.canonical(a) == winner
        assert f.canonical(b) == winner
        assert set(f.classes[winner].node_indices) == {0, 1}

    def test_merge_rank_swap(self) -> None:
        """Ensure loser's nodes go to winner when ranks differ."""
        f = Fiber("test")
        a = f._assign(("a",), (), 0)
        b = f._assign(("b",), (), 1)
        c = f._assign(("c",), (), 2)
        f.merge(a, b)
        winner = f.merge(c, f.canonical(a))
        assert 2 in f.classes[winner].node_indices

    def test_canonical_classes(self) -> None:
        f = Fiber("test")
        a = f._assign(("a",), (), 0)
        b = f._assign(("b",), (), 1)
        assert len(f) == 2
        f.merge(a, b)
        assert len(f) == 1

    def test_getitem(self) -> None:
        f = Fiber("test")
        fid = f._assign(("a",), (), 0)
        assert f[fid].id == fid

    def test_iter(self) -> None:
        f = Fiber("test")
        f._assign(("a",), (), 0)
        f._assign(("b",), (), 1)
        assert len(list(f)) == 2

    def test_repr(self) -> None:
        f = Fiber("sigma")
        assert "Fiber('sigma'" in repr(f)


# ── SPPF basic ───────────────────────────────────────────────────────

class TestSPPF:
    def test_empty(self) -> None:
        s = SPPF()
        assert s.node_count == 0
        assert s.summary() == "SPPF: 0 nodes"

    def test_single_node(self) -> None:
        s = SPPF()
        sid, tid, kid, idx = s._ingest_node(
            "Foo", (("n", "x"),), "int", "var",
            (), (), (), 1, "test.py")
        assert idx == 0
        assert s.node_count == 1
        assert s.nodes[0]['ast_type'] == "Foo"

    def test_wedge(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        s._ingest_node("B", (), "t2", "k2", (), (), (), 1, "f")
        w = s.wedge()
        assert len(w) == 2

    def test_wedge_2(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        w2 = s.wedge_2("sigma", "tau")
        assert len(w2) == 1

    def test_rotate(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        r = s.rotate("sigma", "tau")
        assert len(r) == 1

    def test_rank(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        r = s.rank("sigma", 0, "tau")
        assert r >= 1

    def test_rank_distribution(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        dist = s.rank_distribution("sigma", "tau")
        assert sum(dist.values()) > 0

    def test_hybrid(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        classes, winners = s.hybrid()
        assert len(classes) > 0
        assert sum(winners.values()) == 1

    def test_natural_transformations_empty(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        nt = s.natural_transformations("sigma")
        assert nt == []

    def test_residue(self) -> None:
        s = SPPF()
        _, tid, _, _ = s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        res = s.residue(tid)
        assert "t1" in res

    def test_cleavage_empty(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        assert s.cleavage() == []

    def test_repr(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        r = repr(s)
        assert "SPPF(" in r
        assert "1 nodes" in r

    def test_summary_nonempty(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), "t1", "k1", (), (), (), 0, "f")
        s._ingest_node("B", (), "t2", "k2", (), (), (), 1, "f")
        text = s.summary()
        assert "σ (syntax)" in text
        assert "rank(" in text


# ── SPPF η-detection paths ──────────────────────────────────────────

class TestSPPFEta:
    def test_no_eta_when_dep_type_none(self) -> None:
        s = SPPF()
        s._ingest_node("A", (), None, "k1", (), (), (), 0, "f")
        s._ingest_node("A", (), None, "k2", (), (), (), 1, "f")
        assert s._eta_count == 0

    def test_eta_merge_same_structure_different_dep(self) -> None:
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        assert s._eta_count == 1
        t0 = s.tau.canonical(s.nodes[0]['tau'])
        t1 = s.tau.canonical(s.nodes[1]['tau'])
        assert t0 == t1

    def test_eta_no_merge_same_dep(self) -> None:
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "int", "k2", (), (), (), 1, "f")
        assert s._eta_count == 0

    def test_eta_existing_abs_type_already_present(self) -> None:
        """Third node whose abs_type already exists in structural entry."""
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        s._ingest_node("X", (), "int", "k3", (), (), (), 2, "f")

    def test_eta_with_children(self) -> None:
        s = SPPF()
        _, ct1, _, _ = s._ingest_node("C", (), "a", "leaf", (), (), (), 0, "f")
        s._ingest_node("P", (), "int", "k1", (), (ct1,), (), 1, "f")
        s._ingest_node("P", (), "str", "k2", (), (ct1,), (), 2, "f")
        assert s._eta_count >= 1

    def test_should_merge_false_all_same_canonical(self) -> None:
        """When abs_type not in existing but all existing tids share
        the same canonical as the new tid → should_merge=False."""
        s = SPPF()
        # First two nodes merge
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        assert s._eta_count == 1
        # Third with different dep
        s._ingest_node("X", (), "bool", "k3", (), (), (), 2, "f")
        assert s._eta_count >= 2

    def test_eta_unified_names_gt_1(self) -> None:
        """Exercise the unified_names > 1 branch inside _ingest_node
        by creating a chain of abstractions then triggering a merge
        that unifies existing abstraction names."""
        s = SPPF()
        # Create first η-merge: A+B → ∀η.X.int
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        # Create a different structural group with overlapping types
        _, c1, _, _ = s._ingest_node("C", (), "c1", "cl", (), (), (), 2, "f")
        s._ingest_node("Y", (), "int", "k3", (), (c1,), (), 3, "f")
        s._ingest_node("Y", (), "str", "k4", (), (c1,), (), 4, "f")
        # Both groups abstracted "int" and "str"
        # The abstractions should now be in _eta_abstractions


# ── SPPF cleavage ───────────────────────────────────────────────────

class TestSPPFCleavage:
    def test_cleavage_with_residue(self) -> None:
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        clv = s.cleavage()
        assert len(clv) >= 1
        _, counts, total = clv[0]
        assert total >= 2

    def test_process_cleavage_small_residue_noop(self) -> None:
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        tid = s.nodes[0]['tau']
        s._process_cleavage(tid, "X", 0)

    def test_process_cleavage_two_parents(self) -> None:
        """Two η-merges with the same residue signature trigger
        the cleavage inner logic (len(existing) >= 2)."""
        s = SPPF()
        # Two separate groups with same residue pattern
        _, c1, _, _ = s._ingest_node("C1", (), "c_a", "cl", (), (), (), 0, "f")
        _, c2, _, _ = s._ingest_node("C2", (), "c_b", "cl", (), (), (), 1, "f")

        # Group A: parents over c1
        s._ingest_node("P", (), "int", "k1", (), (c1,), (), 2, "f")
        s._ingest_node("P", (), "str", "k2", (), (c1,), (), 3, "f")
        # η-merge → residue {int, str}, cleavage entry created

        # Group B: parents over c2
        s._ingest_node("P", (), "int", "k3", (), (c2,), (), 4, "f")
        s._ingest_node("P", (), "str", "k4", (), (c2,), (), 5, "f")
        # η-merge → residue {int, str}, same cleavage key → inner logic

    def test_process_cleavage_ghost_direct(self) -> None:
        """Directly exercise ghost cleavage (all same kappa_tag)."""
        s = SPPF()
        # Create two tau classes with nodes that share the same kappa_tag
        tid1 = s.tau._assign(("s1",), (), 0)
        tid2 = s.tau._assign(("s2",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'same_k',
                        'sigma': 0, 'tau': tid1, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'same_k',
                        'sigma': 0, 'tau': tid2, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s._residue_sets[tid1] = {"int", "str"}
        s._residue_sets[tid2] = {"int", "str"}
        # First call creates the entry
        s._process_cleavage(tid1, "X", 0)
        # Second call triggers inner logic
        s._process_cleavage(tid2, "X", 1)
        assert s._cleavage_ghost_count >= 1

    def test_process_cleavage_real_direct(self) -> None:
        """Directly exercise real cleavage (different kappa_tags)."""
        s = SPPF()
        tid1 = s.tau._assign(("s1",), (), 0)
        tid2 = s.tau._assign(("s2",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k_alpha',
                        'sigma': 0, 'tau': tid1, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k_beta',
                        'sigma': 0, 'tau': tid2, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s._residue_sets[tid1] = {"int", "str"}
        s._residue_sets[tid2] = {"int", "str"}
        s._process_cleavage(tid1, "X", 0)
        s._process_cleavage(tid2, "X", 1)
        # Should be real cleavage, not ghost
        real_count = sum(
            1 for e in s._eta_tower
            if isinstance(e[2], str) and e[2].startswith('η-cleavage')
        )
        assert real_count >= 1

    def test_process_cleavage_parent_key_already_in_existing(self) -> None:
        """The parent_key already in existing → break (line 299)."""
        s = SPPF()
        # Manual setup to avoid prior _process_cleavage calls from _ingest_node
        tid1 = s.tau._assign(("s1",), (), 0)
        tid2 = s.tau._assign(("s2",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k1',
                        'sigma': 0, 'tau': tid1, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k2',
                        'sigma': 0, 'tau': tid2, 'kappa': 0, 'line': 1,
                        'file': 'f'})
        s._residue_sets[tid1] = {"int", "str"}
        s._residue_sets[tid2] = {"int", "str"}
        # First call creates the entry
        s._process_cleavage(tid1, "X", 0)
        # Second call adds tid2 → len(existing) >= 2
        s._process_cleavage(tid2, "X", 1)
        # Third call with tid1 AGAIN → parent_key already in existing → break
        s._process_cleavage(tid1, "X", 2)

    def test_process_cleavage_multi_level(self) -> None:
        """Multiple τ-classes with same residue but next_residue >= 2
        triggers multi-level cleavage."""
        s = SPPF()
        # Create 3 separate child taus
        _, c1, _, _ = s._ingest_node("C1", (), "ca", "cl", (), (), (), 0, "f")
        _, c2, _, _ = s._ingest_node("C2", (), "cb", "cl", (), (), (), 1, "f")
        _, c3, _, _ = s._ingest_node("C3", (), "cc", "cl", (), (), (), 2, "f")
        # Group over c1
        s._ingest_node("P", (), "int", "ka", (), (c1,), (), 3, "f")
        s._ingest_node("P", (), "str", "kb", (), (c1,), (), 4, "f")
        # Group over c2
        s._ingest_node("P", (), "int", "kc", (), (c2,), (), 5, "f")
        s._ingest_node("P", (), "str", "kd", (), (c2,), (), 6, "f")
        # Group over c3
        s._ingest_node("P", (), "int", "ke", (), (c3,), (), 7, "f")
        s._ingest_node("P", (), "str", "kf", (), (c3,), (), 8, "f")

    def test_cleavage_with_eta_abstractions(self) -> None:
        """Exercise the contained_2cells logic in cleavage where
        _eta_abstractions has entries."""
        s = SPPF()
        # Create η-merge so _eta_abstractions is populated
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        # Now create separate groups with same residue to trigger cleavage
        _, c1, _, _ = s._ingest_node("C1", (), "c1", "cl", (), (), (), 2, "f")
        _, c2, _, _ = s._ingest_node("C2", (), "c2", "cl", (), (), (), 3, "f")
        s._ingest_node("P", (), "int", "k3", (), (c1,), (), 4, "f")
        s._ingest_node("P", (), "str", "k4", (), (c1,), (), 5, "f")
        s._ingest_node("P", (), "int", "k5", (), (c2,), (), 6, "f")
        s._ingest_node("P", (), "str", "k6", (), (c2,), (), 7, "f")

    def test_cleavage_node_index_out_of_range(self) -> None:
        """Exercise the ni >= len(self.nodes) guard."""
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        canon_tid = s.tau.canonical(s.nodes[0]['tau'])
        # Append a bogus node_index to the tau class
        s.tau.classes[canon_tid].node_indices.append(9999)
        # Ensure residue has >= 2 entries
        s._residue_sets[canon_tid] = {"int", "str"}
        # Create cleavage level and a prior entry
        s._cleavage_levels.append({})
        s._cleavage_fibers.append(Fiber("test_cleavage"))
        cleavage_key = ("X", tuple(sorted(["int", "str"])))
        s._cleavage_levels[0][cleavage_key] = {canon_tid + 100: canon_tid + 100}
        # Now call _process_cleavage → should not crash
        s._process_cleavage(canon_tid, "X", 0)

    def test_cleavage_bogus_node_index(self) -> None:
        """Exercise `if ni >= len(self.nodes)` True guard (line 286)."""
        s = SPPF()
        tid_real = s.tau._assign(("real",), (), 0)
        tid_other = s.tau._assign(("other",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k1',
                        'sigma': 0, 'tau': tid_real, 'kappa': 0,
                        'line': 0, 'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k2',
                        'sigma': 0, 'tau': tid_other, 'kappa': 0,
                        'line': 1, 'file': 'f'})
        # Add a bogus node index to tid_real's class
        s.tau.classes[tid_real].node_indices.append(9999)
        s._residue_sets[tid_real] = {"int", "str"}
        s._residue_sets[tid_other] = {"int", "str"}
        # Two calls to get len(existing) >= 2
        s._process_cleavage(tid_real, "X", 0)
        s._process_cleavage(tid_other, "X", 1)

    def test_cleavage_with_abstractions_and_uf(self) -> None:
        """Exercise abs_name in _eta_uf → find() path in cleavage."""
        s = SPPF()
        tid1 = s.tau._assign(("s1",), (), 0)
        tid2 = s.tau._assign(("s2",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k1',
                        'sigma': 0, 'tau': tid1, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k2',
                        'sigma': 0, 'tau': tid2, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        # Residues that include an abstracted type
        s._eta_abstractions["a"] = "abs_a"
        s._eta_uf.make("abs_a")
        s._residue_sets[tid1] = {"a", "b"}
        s._residue_sets[tid2] = {"a", "b"}
        s._process_cleavage(tid1, "X", 0)
        s._process_cleavage(tid2, "X", 1)

    def test_cleavage_abs_name_not_in_uf(self) -> None:
        """Exercise abs_name NOT in _eta_uf (else branch)."""
        s = SPPF()
        tid1 = s.tau._assign(("s1",), (), 0)
        tid2 = s.tau._assign(("s2",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k1',
                        'sigma': 0, 'tau': tid1, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k2',
                        'sigma': 0, 'tau': tid2, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s._eta_abstractions["a"] = "abs_no_uf"
        # abs_no_uf NOT in _eta_uf
        s._residue_sets[tid1] = {"a", "b"}
        s._residue_sets[tid2] = {"a", "b"}
        s._process_cleavage(tid1, "X", 0)
        s._process_cleavage(tid2, "X", 1)

    def test_cleavage_node_already_annotated(self) -> None:
        """Exercise the 'cleavage_N already in node' skip branch."""
        s = SPPF()
        tid1 = s.tau._assign(("s1",), (), 0)
        tid2 = s.tau._assign(("s2",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k1',
                        'sigma': 0, 'tau': tid1, 'kappa': 0, 'line': 0,
                        'file': 'f', 'cleavage_0': 42})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k2',
                        'sigma': 0, 'tau': tid2, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s._residue_sets[tid1] = {"int", "str"}
        s._residue_sets[tid2] = {"int", "str"}
        s._process_cleavage(tid1, "X", 0)
        s._process_cleavage(tid2, "X", 1)

    def test_cleavage_next_residue_multi_level(self) -> None:
        """Exercise next_residue >= 2 → multi-level continue path."""
        s = SPPF()
        # Create 3 tau classes to get next_residue of length >= 2
        tid1 = s.tau._assign(("s1",), (), 0)
        tid2 = s.tau._assign(("s2",), (), 1)
        tid3 = s.tau._assign(("s3",), (), 2)
        for i, tid in enumerate([tid1, tid2, tid3]):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f't{i}',
                            'dep_type_raw': f't{i}', 'kappa_tag': f'k{i}',
                            'sigma': 0, 'tau': tid, 'kappa': 0, 'line': i,
                            'file': 'f'})
        s._residue_sets[tid1] = {"a", "b"}
        s._residue_sets[tid2] = {"a", "b"}
        s._residue_sets[tid3] = {"a", "b"}
        # First two create and fill an entry
        s._process_cleavage(tid1, "X", 0)
        s._process_cleavage(tid2, "X", 1)
        # Third adds another parent → next_residue includes tid1, tid2, tid3
        # which are all distinct canonicals → len >= 2 → multi-level
        s._process_cleavage(tid3, "X", 2)

    def test_cleavage_class_id_increments_per_event(self) -> None:
        """Distinct same-level cleavage events should use distinct ids."""
        s = SPPF()

        tid1 = s.tau._assign(("x1",), (), 0)
        tid2 = s.tau._assign(("x2",), (), 1)
        tid3 = s.tau._assign(("y1",), (), 2)
        tid4 = s.tau._assign(("y2",), (), 3)

        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k1',
                        'sigma': 0, 'tau': tid1, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k2',
                        'sigma': 0, 'tau': tid2, 'kappa': 0, 'line': 1,
                        'file': 'f'})
        s.nodes.append({'ast_type': 'Y', 'params': (), 'dep_type': 'c',
                        'dep_type_raw': 'c', 'kappa_tag': 'k3',
                        'sigma': 0, 'tau': tid3, 'kappa': 0, 'line': 2,
                        'file': 'f'})
        s.nodes.append({'ast_type': 'Y', 'params': (), 'dep_type': 'd',
                        'dep_type_raw': 'd', 'kappa_tag': 'k4',
                        'sigma': 0, 'tau': tid4, 'kappa': 0, 'line': 3,
                        'file': 'f'})

        s._residue_sets[tid1] = {"int", "str"}
        s._residue_sets[tid2] = {"int", "str"}
        s._residue_sets[tid3] = {"int", "str"}
        s._residue_sets[tid4] = {"int", "str"}

        # First cleavage event at level 0 for context X.
        s._process_cleavage(tid1, "X", 0)
        s._process_cleavage(tid2, "X", 1)

        # Second cleavage event at level 0 for context Y.
        s._process_cleavage(tid3, "Y", 2)
        s._process_cleavage(tid4, "Y", 3)

        x_id = s.nodes[0]["cleavage_0"]
        y_id = s.nodes[2]["cleavage_0"]
        assert x_id != y_id


# ── SPPF cascading ──────────────────────────────────────────────────

class TestSPPFCascade:
    def test_cascade_eta_empty_worklist(self) -> None:
        """Valid tau IDs but no structural key parents → no-op."""
        s = SPPF()
        _, tid, _, _ = s._ingest_node("X", (), "t", "k", (), (), (), 0, "f")
        s._cascade_eta({tid}, 0)  # Should not crash

    def test_seed_worklist_valid(self) -> None:
        s = SPPF()
        _, tid, _, _ = s._ingest_node("X", (), "t", "k", (), (), (), 0, "f")
        target: set[tuple[str, tuple[int, ...]]] = set()
        s._seed_worklist({tid}, target)

    def test_seed_worklist_with_non_canonical(self) -> None:
        """Tau ID that is not canonical → also looks up canonical."""
        s = SPPF()
        _, t1, _, _ = s._ingest_node("X", (), "a", "k", (), (), (), 0, "f")
        _, t2, _, _ = s._ingest_node("X", (), "b", "k", (), (), (), 1, "f")
        # t1 and t2 are now merged; use the non-canonical one
        canon = s.tau.canonical(t1)
        non_canon = t1 if t1 != canon else t2
        target: set[tuple[str, tuple[int, ...]]] = set()
        s._seed_worklist({non_canon}, target)

    def test_cascade_eta_changed_true_key_collision(self) -> None:
        """Structural key re-canon collides with existing key."""
        s = SPPF()
        # Child c1 (will be non-canonical after merge)
        _, c1, _, _ = s._ingest_node("C", (), "c_type", "cl", (), (), (), 0, "f")
        # Parent keyed on c1
        s._ingest_node("P", (), "dep_a", "pa", (), (c1,), (), 1, "f")

        # Build a c2 with higher rank by pre-merging
        _, c2a, _, _ = s._ingest_node("D", (), "d1", "dl", (), (), (), 2, "f")
        _, c2b, _, _ = s._ingest_node("D", (), "d2", "dl", (), (), (), 3, "f")
        c2_canon = s.tau.canonical(c2a)  # c2a absorbed c2b, rank 1

        # Parent keyed on c2_canon
        s._ingest_node("P", (), "dep_a", "pa", (), (c2_canon,), (), 4, "f")

        # Now manually merge c1 into c2_canon (c2 wins since higher rank)
        s._merge_residue_sets(c2_canon, c1)
        s.tau.merge(c2_canon, c1)
        # c1 now re-canonicalizes to c2_canon
        # Trigger cascade: ("P", (c1,)) → ("P", (c2_canon,)) which already exists
        s._cascade_eta({c1, c2_canon}, 0)

    def test_cascade_eta_changed_true_no_collision(self) -> None:
        """Structural key re-canon moves to a new location (no collision)."""
        s = SPPF()
        _, c1, _, _ = s._ingest_node("C", (), "ct", "cl", (), (), (), 0, "f")
        # Build c2 with higher rank
        _, c2a, _, _ = s._ingest_node("D", (), "d1", "dl", (), (), (), 1, "f")
        _, c2b, _, _ = s._ingest_node("D", (), "d2", "dl", (), (), (), 2, "f")
        c2_canon = s.tau.canonical(c2a)

        # Parent keyed only on c1
        s._ingest_node("P", (), "dep_x", "pa", (), (c1,), (), 3, "f")

        # Merge c1 into c2_canon
        s._merge_residue_sets(c2_canon, c1)
        s.tau.merge(c2_canon, c1)
        # ("P", (c1,)) → ("P", (c2_canon,)) which doesn't exist
        s._cascade_eta({c1, c2_canon}, 0)

    def test_cascade_eta_changed_false_dep_abstract_merge(self) -> None:
        """changed=False but dep variants resolve to same key → merge."""
        s = SPPF()
        _, c1, _, _ = s._ingest_node("C", (), "ct", "cl", (), (), (), 0, "f")
        # Two parents with different dep types but same struct key
        s._ingest_node("P", (), "dep_a", "pa", (), (c1,), (), 1, "f")
        s._ingest_node("P", (), "dep_b", "pb", (), (c1,), (), 2, "f")
        # Now make dep_a and dep_b resolve to the same thing
        s._eta_abstractions["dep_a"] = "unified"
        s._eta_abstractions["dep_b"] = "unified"
        s._eta_uf.make("unified")
        # Trigger cascade (c1 didn't change, so changed=False)
        s._cascade_eta({c1}, 0)

    def test_cascade_eta_second_order(self) -> None:
        """Exercise ∀η² (second-order abstraction) inside _cascade_eta
        when multiple distinct canonical tids exist after rekeying."""
        s = SPPF()
        # Create two children
        _, c1, _, _ = s._ingest_node("C", (), "ct1", "cl", (), (), (), 0, "f")
        # Build c2 with higher rank via pre-merge
        _, c2a, _, _ = s._ingest_node("D", (), "d1", "dl", (), (), (), 1, "f")
        _, c2b, _, _ = s._ingest_node("D", (), "d2", "dl", (), (), (), 2, "f")
        c2_canon = s.tau.canonical(c2a)

        # Parents with multiple dep types over c1
        s._ingest_node("P", (), "alpha", "pa", (), (c1,), (), 3, "f")
        s._ingest_node("P", (), "beta", "pb", (), (c1,), (), 4, "f")

        # Parents with same dep types over c2_canon
        s._ingest_node("P", (), "alpha", "pa", (), (c2_canon,), (), 5, "f")
        s._ingest_node("P", (), "beta", "pb", (), (c2_canon,), (), 6, "f")

        # Merge c1 into c2_canon → keys collide → ∀η² triggered
        s._merge_residue_sets(c2_canon, c1)
        s.tau.merge(c2_canon, c1)
        s._cascade_eta({c1, c2_canon}, 0)

    def test_cascade_abstraction_merge_empty(self) -> None:
        s = SPPF()
        result = s._cascade_abstraction_merge({"nonexistent"}, 0)
        assert result == set()

    def test_cascade_abstraction_merge_with_merges(self) -> None:
        """Directly test _cascade_abstraction_merge with prepared state.
        merged_names must include the variant names in _tau_structural_by_variant."""
        s = SPPF()
        tid1 = s.tau._assign(("sig1",), (), 0)
        tid2 = s.tau._assign(("sig2",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k', 'sigma': 0,
                        'tau': tid1, 'kappa': 0, 'line': 0, 'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k', 'sigma': 0,
                        'tau': tid2, 'kappa': 0, 'line': 0, 'file': 'f'})
        struct_key: tuple[str, tuple[int, ...]] = ("X", ())
        # Variants are stored under their resolved names
        s._tau_structural[struct_key] = {"resolved_a": tid1, "resolved_b": tid2}
        s._tau_structural_by_variant["resolved_a"] = {struct_key}
        s._tau_structural_by_variant["resolved_b"] = {struct_key}
        # Both resolve to "merged" via _eta_abstractions + _eta_uf
        s._eta_abstractions["resolved_a"] = "merged"
        s._eta_abstractions["resolved_b"] = "merged"
        s._eta_uf.make("merged")
        # Pass the VARIANT names that are in the by_variant index
        result = s._cascade_abstraction_merge(
            {"resolved_a", "resolved_b", "merged"}, 0)
        assert len(result) >= 1

    def test_cascade_abstraction_merge_no_merges(self) -> None:
        """Variants resolve to different keys → no merge."""
        s = SPPF()
        tid1 = s.tau._assign(("sig1",), (), 0)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k', 'sigma': 0,
                        'tau': tid1, 'kappa': 0, 'line': 0, 'file': 'f'})
        struct_key: tuple[str, tuple[int, ...]] = ("X", ())
        s._tau_structural[struct_key] = {"only_a": tid1}
        s._tau_structural_by_variant["only_a"] = {struct_key}
        s._eta_abstractions["only_a"] = "resolved_a"
        s._eta_uf.make("resolved_a")
        result = s._cascade_abstraction_merge({"resolved_a"}, 0)
        assert result == set()

    def test_cascade_abstraction_merge_struct_key_deleted(self) -> None:
        """Affected struct_key not in _tau_structural → skip."""
        s = SPPF()
        struct_key: tuple[str, tuple[int, ...]] = ("X", ())
        s._tau_structural_by_variant["name_a"] = {struct_key}
        # struct_key not in _tau_structural
        result = s._cascade_abstraction_merge({"name_a"}, 0)
        assert result == set()

    def test_cascade_eta_rekey_collision(self) -> None:
        """Exercise the rekey_collision branch in the bug-fix area.
        Two variants in a moved key resolve to the same type."""
        s = SPPF()
        # Create tau classes
        tid_a = s.tau._assign(("sig_a",), (), 0)
        tid_b = s.tau._assign(("sig_b",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'a',
                        'dep_type_raw': 'a', 'kappa_tag': 'k', 'sigma': 0,
                        'tau': tid_a, 'kappa': 0, 'line': 0, 'file': 'f'})
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'b',
                        'dep_type_raw': 'b', 'kappa_tag': 'k', 'sigma': 0,
                        'tau': tid_b, 'kappa': 0, 'line': 0, 'file': 'f'})

        # Create a child tau that will cause re-canon
        child_old = s.tau._assign(("child_old",), (), 2)
        # Build child_new with higher rank
        child_new_a = s.tau._assign(("child_new_a",), (), 3)
        child_new_b = s.tau._assign(("child_new_b",), (), 4)
        s.tau.merge(child_new_a, child_new_b)
        child_new = s.tau.canonical(child_new_a)

        # Structural key uses child_old
        struct_key: tuple[str, tuple[int, ...]] = ("P", (child_old,))
        s._tau_structural[struct_key] = {"var_a": tid_a, "var_b": tid_b}
        s._tau_structural_by_variant["var_a"] = {struct_key}
        s._tau_structural_by_variant["var_b"] = {struct_key}
        s._tau_structural_by_child[child_old] = {struct_key}

        # Make both variants resolve to the same thing
        s._eta_abstractions["var_a"] = "same_resolved"
        s._eta_abstractions["var_b"] = "same_resolved"
        s._eta_uf.make("same_resolved")

        # Merge child_old into child_new → key changes
        s.tau.merge(child_new, child_old)
        # Now ("P", (child_old,)) re-canons to ("P", (child_new,))
        # and the two variants collide
        s._cascade_eta({child_old, child_new}, 0)

    def test_cascade_eta_key_collision_with_existing(self) -> None:
        """Moved key collides with pre-existing entry at new_key.
        Exercises the collision branch AND the else (new variant) branch."""
        s = SPPF()
        tid_1 = s.tau._assign(("t1",), (), 0)
        tid_2 = s.tau._assign(("t2",), (), 1)
        tid_3 = s.tau._assign(("t3",), (), 2)
        for i in range(3):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f'd{i}',
                            'dep_type_raw': f'd{i}', 'kappa_tag': 'k',
                            'sigma': 0, 'tau': i, 'kappa': 0, 'line': i,
                            'file': 'f'})

        child_old = s.tau._assign(("cold",), (), 3)
        child_new_a = s.tau._assign(("cnew_a",), (), 4)
        child_new_b = s.tau._assign(("cnew_b",), (), 5)
        s.tau.merge(child_new_a, child_new_b)
        child_new = s.tau.canonical(child_new_a)

        old_key: tuple[str, tuple[int, ...]] = ("P", (child_old,))
        # old key has variants "dep_x" AND "dep_new" (dep_new won't exist in target)
        s._tau_structural[old_key] = {"dep_x": tid_1, "dep_new": tid_3}
        s._tau_structural_by_child[child_old] = {old_key}

        new_key: tuple[str, tuple[int, ...]] = ("P", (child_new,))
        # Target has "dep_x" (collision) but NOT "dep_new" (else branch)
        s._tau_structural[new_key] = {"dep_x": tid_2}
        s._tau_structural_by_child[child_new] = {new_key}

        s.tau.merge(child_new, child_old)
        s._cascade_eta({child_old, child_new}, 0)

    def test_cascade_eta_changed_false_no_dep_merge(self) -> None:
        """changed=False with no dep collisions → merges_here empty → continue."""
        s = SPPF()
        tid_a = s.tau._assign(("ta",), (), 0)
        child = s.tau._assign(("child",), (), 1)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'd0',
                        'dep_type_raw': 'd0', 'kappa_tag': 'k',
                        'sigma': 0, 'tau': 0, 'kappa': 0, 'line': 0, 'file': 'f'})
        s.nodes.append({'ast_type': 'C', 'params': (), 'dep_type': 'c',
                        'dep_type_raw': 'c', 'kappa_tag': 'k',
                        'sigma': 0, 'tau': 1, 'kappa': 0, 'line': 1, 'file': 'f'})
        struct_key: tuple[str, tuple[int, ...]] = ("P", (child,))
        # Single variant → no collision possible → merges_here stays empty
        s._tau_structural[struct_key] = {"only_var": tid_a}
        s._tau_structural_by_variant["only_var"] = {struct_key}
        s._tau_structural_by_child[child] = {struct_key}
        s._cascade_eta({child}, 0)

    def test_cascade_eta_deleted_key_in_worklist(self) -> None:
        """Exercise old_key not in _tau_structural (key deleted during cascade)."""
        s = SPPF()
        tid = s.tau._assign(("t",), (), 0)
        s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': 'd',
                        'dep_type_raw': 'd', 'kappa_tag': 'k',
                        'sigma': 0, 'tau': tid, 'kappa': 0, 'line': 0,
                        'file': 'f'})
        # Register a structural key that's in the child index but NOT in _tau_structural
        phantom_key: tuple[str, tuple[int, ...]] = ("P", (tid,))
        s._tau_structural_by_child[tid] = {phantom_key}
        # _tau_structural does NOT have phantom_key → should skip
        s._cascade_eta({tid}, 0)

    def test_cascade_eta_changed_false_with_dep_merge(self) -> None:
        """changed=False path where two variants resolve to the same dep_type,
        triggering a τ-merge (dep_abstract merge)."""
        s = SPPF()
        tid_a = s.tau._assign(("ta",), (), 0)
        tid_b = s.tau._assign(("tb",), (), 1)
        child = s.tau._assign(("child",), (), 2)
        for i in range(2):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f'd{i}',
                            'dep_type_raw': f'd{i}', 'kappa_tag': 'k',
                            'sigma': 0, 'tau': i, 'kappa': 0, 'line': i,
                            'file': 'f'})
        s.nodes.append({'ast_type': 'C', 'params': (), 'dep_type': 'c',
                        'dep_type_raw': 'c', 'kappa_tag': 'k',
                        'sigma': 0, 'tau': child, 'kappa': 0, 'line': 2,
                        'file': 'f'})
        struct_key: tuple[str, tuple[int, ...]] = ("P", (child,))
        s._tau_structural[struct_key] = {"var_a": tid_a, "var_b": tid_b}
        s._tau_structural_by_variant["var_a"] = {struct_key}
        s._tau_structural_by_variant["var_b"] = {struct_key}
        s._tau_structural_by_child[child] = {struct_key}
        # Make both variants resolve to the same thing
        s._eta_abstractions["var_a"] = "same"
        s._eta_abstractions["var_b"] = "same"
        s._eta_uf.make("same")
        # Trigger cascade with child (key unchanged = changed=False)
        s._cascade_eta({child}, 0)
        # Should have merged tid_a and tid_b
        assert s.tau.canonical(tid_a) == s.tau.canonical(tid_b)

    def test_cascade_eta_second_order_full(self) -> None:
        """Exercise the full ∀η² path: changed=True, new key doesn't
        exist, multiple distinct canonical tids after rekeying."""
        s = SPPF()
        tid_1 = s.tau._assign(("t1",), (), 0)
        tid_2 = s.tau._assign(("t2",), (), 1)
        for i in range(2):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f'd{i}',
                            'dep_type_raw': f'd{i}', 'kappa_tag': f'k{i}',
                            'sigma': 0, 'tau': i, 'kappa': 0, 'line': i,
                            'file': 'f'})

        # Child that will be non-canonical after merge
        child_old = s.tau._assign(("cold",), (), 2)
        child_new_a = s.tau._assign(("cnew_a",), (), 3)
        child_new_b = s.tau._assign(("cnew_b",), (), 4)
        s.tau.merge(child_new_a, child_new_b)
        child_new = s.tau.canonical(child_new_a)

        struct_key: tuple[str, tuple[int, ...]] = ("P", (child_old,))
        s._tau_structural[struct_key] = {"dep_x": tid_1, "dep_y": tid_2}
        s._tau_structural_by_variant["dep_x"] = {struct_key}
        s._tau_structural_by_variant["dep_y"] = {struct_key}
        s._tau_structural_by_child[child_old] = {struct_key}

        s.tau.merge(child_new, child_old)
        # Now old_key recanons to ("P", (child_new,)) which doesn't exist
        # And tid_1 != tid_2 → ∀η² triggered
        s._cascade_eta({child_old, child_new}, 0)

    def test_cascade_eta_second_order_with_unified_names(self) -> None:
        """∀η² where resolved types are already in _eta_uf,
        triggering unified_names_2 > 1 and cascade_abstraction_merge."""
        s = SPPF()
        tid_1 = s.tau._assign(("t1",), (), 0)
        tid_2 = s.tau._assign(("t2",), (), 1)
        for i in range(2):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f'd{i}',
                            'dep_type_raw': f'd{i}', 'kappa_tag': f'k{i}',
                            'sigma': 0, 'tau': i, 'kappa': 0, 'line': i,
                            'file': 'f'})

        child_old = s.tau._assign(("cold",), (), 2)
        child_new_a = s.tau._assign(("cnew_a",), (), 3)
        child_new_b = s.tau._assign(("cnew_b",), (), 4)
        s.tau.merge(child_new_a, child_new_b)
        child_new = s.tau.canonical(child_new_a)

        struct_key: tuple[str, tuple[int, ...]] = ("P", (child_old,))
        s._tau_structural[struct_key] = {"dep_x": tid_1, "dep_y": tid_2}
        s._tau_structural_by_variant["dep_x"] = {struct_key}
        s._tau_structural_by_variant["dep_y"] = {struct_key}
        s._tau_structural_by_child[child_old] = {struct_key}

        # Pre-register resolved types in _eta_uf so they get unified
        s._eta_uf.make("dep_x")
        s._eta_uf.make("dep_y")

        s.tau.merge(child_new, child_old)
        s._cascade_eta({child_old, child_new}, 0)

    def test_cascade_eta_second_order_dup_canon(self) -> None:
        """Exercise canon_tids with duplicate canonical (531->529 False)
        and resolved == eta_name (543->541 False)."""
        s = SPPF()
        # Two tids that share canonical (via pre-merge)
        tid_1 = s.tau._assign(("t1",), (), 0)
        tid_2 = s.tau._assign(("t2",), (), 1)
        s.tau.merge(tid_1, tid_2)  # Now both canonical = tid_1
        for i in range(2):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f'd{i}',
                            'dep_type_raw': f'd{i}', 'kappa_tag': f'k{i}',
                            'sigma': 0, 'tau': i, 'kappa': 0, 'line': i,
                            'file': 'f'})

        child_old = s.tau._assign(("cold",), (), 2)
        child_new_a = s.tau._assign(("cnew_a",), (), 3)
        child_new_b = s.tau._assign(("cnew_b",), (), 4)
        s.tau.merge(child_new_a, child_new_b)
        child_new = s.tau.canonical(child_new_a)

        struct_key: tuple[str, tuple[int, ...]] = ("P", (child_old,))
        # Two variants point to tids that share the same canonical
        s._tau_structural[struct_key] = {"dep_x": tid_1, "dep_y": tid_2}
        s._tau_structural_by_variant["dep_x"] = {struct_key}
        s._tau_structural_by_variant["dep_y"] = {struct_key}
        s._tau_structural_by_child[child_old] = {struct_key}

        s.tau.merge(child_new, child_old)
        s._cascade_eta({child_old, child_new}, 0)

    def test_cascade_eta_rekey_resolved_equals_eta_name(self) -> None:
        """∀η² where a resolved type happens to equal the eta_name."""
        s = SPPF()
        tid_1 = s.tau._assign(("t1",), (), 0)
        tid_2 = s.tau._assign(("t2",), (), 1)
        for i in range(2):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f'd{i}',
                            'dep_type_raw': f'd{i}', 'kappa_tag': f'k{i}',
                            'sigma': 0, 'tau': i, 'kappa': 0, 'line': i,
                            'file': 'f'})

        child_old = s.tau._assign(("cold",), (), 2)
        child_new_a = s.tau._assign(("cnew_a",), (), 3)
        child_new_b = s.tau._assign(("cnew_b",), (), 4)
        s.tau.merge(child_new_a, child_new_b)
        child_new = s.tau.canonical(child_new_a)

        struct_key: tuple[str, tuple[int, ...]] = ("P", (child_old,))
        # Use a dep name that will match the generated eta_name pattern
        # eta_name = f"∀η².{all_types[0]}" — if first type is "dep_x",
        # eta_name = "∀η².dep_x"
        # Make dep_x already resolve to "∀η².dep_x" so resolved == eta_name
        s._eta_abstractions["dep_x"] = "∀η².dep_x"
        s._eta_uf.make("∀η².dep_x")
        s._tau_structural[struct_key] = {"dep_x": tid_1, "dep_y": tid_2}
        s._tau_structural_by_variant["dep_x"] = {struct_key}
        s._tau_structural_by_variant["dep_y"] = {struct_key}
        s._tau_structural_by_child[child_old] = {struct_key}

        s.tau.merge(child_new, child_old)
        s._cascade_eta({child_old, child_new}, 0)

    def test_ingest_should_merge_false(self) -> None:
        """Force should_merge=False: abs_type not in existing but
        all existing tids share canonical with new tid.
        This requires pre-merging the new tid with the existing group."""
        s = SPPF()
        # Ingest first node → creates structural entry
        s._ingest_node("X", (), "type_a", "k1", (), (), (), 0, "f")
        # Ingest second → η-merge, both now share canonical
        s._ingest_node("X", (), "type_b", "k2", (), (), (), 1, "f")
        merged_canon = s.tau.canonical(s.nodes[0]['tau'])
        # Now manually add the NEXT tau class to the same canonical group
        # by pre-creating its signature and merging
        next_abs = s._resolve_type("type_c")  # "type_c" → "type_c" (no abstraction)
        tau_sig = ("X", next_abs, ())
        future_tid = s.tau._assign(tau_sig, (), 999)
        # Merge future_tid into the existing group
        s.tau.merge(merged_canon, future_tid)
        # Now ingest a node with "type_c" — its tau class is future_tid
        # which is already canonical-equivalent to the existing group
        s._ingest_node("X", (), "type_c", "k3", (), (), (), 2, "f")

    def test_cascade_abstraction_merge_cross_key_stale(self) -> None:
        """R6: Cross-key τ-collisions via dynamic canonical() — order-insensitive.

        Two structural keys share variant "v2" → tid_b.  All three variants
        resolve to the same name ("unified").  Regardless of which key the
        set iterator visits first, canonical() is called dynamically inside
        the merge loop, so the merge transitively unifies all three τ-ids:
        whichever key is processed first merges two of {tid_a, tid_b, tid_c};
        the second key then sees the updated canonical and merges the third.

        This validates that R1 (scan-order dependency) is NOT a correctness
        bug in the current implementation.
        """
        s = SPPF()
        tid_a = s.tau._assign(("ta",), (), 0)
        tid_b = s.tau._assign(("tb",), (), 1)
        tid_c = s.tau._assign(("tc",), (), 2)
        for i in range(3):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f'd{i}',
                            'dep_type_raw': f'd{i}', 'kappa_tag': f'k{i}',
                            'sigma': 0, 'tau': i, 'kappa': 0, 'line': i,
                            'file': 'f'})
        key_1: tuple[str, tuple[int, ...]] = ("P", ())
        key_2: tuple[str, tuple[int, ...]] = ("Q", ())
        # key_1: "v1" → tid_a, "v2" → tid_b
        s._tau_structural[key_1] = {"v1": tid_a, "v2": tid_b}
        s._tau_structural_by_variant["v1"] = {key_1}
        s._tau_structural_by_variant["v2"] = {key_1, key_2}
        # key_2: "v2" → tid_b, "v3" → tid_c
        s._tau_structural[key_2] = {"v2": tid_b, "v3": tid_c}
        s._tau_structural_by_variant["v3"] = {key_2}
        # All three variants resolve to "unified"
        s._eta_abstractions["v1"] = "unified"
        s._eta_abstractions["v2"] = "unified"
        s._eta_abstractions["v3"] = "unified"
        s._eta_uf.make("unified")

        s._cascade_abstraction_merge({"v1", "v2", "v3", "unified"}, 0)

        assert s.tau.canonical(tid_a) == s.tau.canonical(tid_b)
        assert s.tau.canonical(tid_b) == s.tau.canonical(tid_c)

    def test_cascade_eta_second_order_abstraction_merge_before_tau_merge(
            self) -> None:
        """R2: ∀η² calls _cascade_abstraction_merge before τ-merges.

        Verifies the ordering is self-healing: tid_1 and tid_2 are merged
        in the final state even though _cascade_abstraction_merge runs with
        pre-merge canonicals.  The subsequent τ-merges (lines 553–559) and
        `_seed_worklist`'s dual-canonical lookup guarantee correctness.
        """
        s = SPPF()
        tid_1 = s.tau._assign(("t1",), (), 0)
        tid_2 = s.tau._assign(("t2",), (), 1)
        for i in range(2):
            s.nodes.append({'ast_type': 'X', 'params': (), 'dep_type': f'd{i}',
                            'dep_type_raw': f'd{i}', 'kappa_tag': f'k{i}',
                            'sigma': 0, 'tau': i, 'kappa': 0, 'line': i,
                            'file': 'f'})
        child_old = s.tau._assign(("cold",), (), 2)
        child_new_a = s.tau._assign(("cna",), (), 3)
        child_new_b = s.tau._assign(("cnb",), (), 4)
        s.tau.merge(child_new_a, child_new_b)
        child_new = s.tau.canonical(child_new_a)

        struct_key: tuple[str, tuple[int, ...]] = ("P", (child_old,))
        s._tau_structural[struct_key] = {"dep_x": tid_1, "dep_y": tid_2}
        s._tau_structural_by_variant["dep_x"] = {struct_key}
        s._tau_structural_by_variant["dep_y"] = {struct_key}
        s._tau_structural_by_child[child_old] = {struct_key}
        # Pre-union dep_x and dep_y in _eta_uf → unified_names_2 > 1 inside
        # the ∀η² block, so _cascade_abstraction_merge is called BEFORE the
        # τ-merges that unify tid_1 and tid_2.
        s._eta_uf.make("dep_x")
        s._eta_uf.make("dep_y")
        s._eta_uf.union("dep_x", "dep_y")

        s.tau.merge(child_new, child_old)
        s._cascade_eta({child_old, child_new}, 0)

        # Despite the ordering, the worklist self-heals: tid_1 and tid_2
        # are merged by the τ-merge block that runs after _cascade_abstraction_merge.
        assert s.tau.canonical(tid_1) == s.tau.canonical(tid_2)


# ── SPPF natural transformations ─────────────────────────────────────

class TestSPPFNaturalTransformations:
    def test_nt_with_multi_rank(self) -> None:
        s = SPPF()
        s._ingest_node("X", (("n", "foo"),), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (("n", "foo"),), "str", "k2", (), (), (), 1, "f")
        s._ingest_node("Y", (("n", "foo"),), "int", "k1", (), (), (), 2, "f")
        nt = s.natural_transformations("kappa")
        for fid, ranks in nt:
            assert all(r > 1 for r in ranks.values())


# ── SPPF observe_cell ────────────────────────────────────────────────

class TestObserveCell:
    def test_observe_no_children(self) -> None:
        s = SPPF()
        s._observe_cell(0, "cell_a")
        assert s._cell_obs[0]["cell_a"] == 1

    def test_observe_with_children(self) -> None:
        s = SPPF()
        s._observe_cell(1, "parent", ["child_a", "child_b"])
        assert s._cell_obs[1]["parent"] == 1
        assert s._cell_obs[0]["child_a"] == 1
        assert s._cell_obs[0]["child_b"] == 1

    def test_observe_recursive(self) -> None:
        s = SPPF()
        s._cell_contents[(1, "mid")] = {"leaf"}
        s._observe_cell(2, "top", ["mid"])
        assert s._cell_obs[2]["top"] == 1
        assert s._cell_obs[1]["mid"] == 1
        assert s._cell_obs[0]["leaf"] == 1

    def test_observe_no_prior_contents(self) -> None:
        """level > 0 but no _cell_contents for this key."""
        s = SPPF()
        s._observe_cell(1, "orphan")
        assert s._cell_obs[1]["orphan"] == 1


# ── SPPF resolve_type ────────────────────────────────────────────────

class TestResolveType:
    def test_none(self) -> None:
        s = SPPF()
        assert s._resolve_type(None) is None

    def test_no_abstraction(self) -> None:
        s = SPPF()
        assert s._resolve_type("int") == "int"

    def test_with_abstraction(self) -> None:
        s = SPPF()
        s._eta_abstractions["int"] = "∀η.X.int"
        s._eta_uf.make("∀η.X.int")
        assert s._resolve_type("int") == "∀η.X.int"

    def test_with_chained_abstraction(self) -> None:
        s = SPPF()
        s._eta_abstractions["int"] = "abs1"
        s._eta_uf.make("abs1")
        s._eta_uf.make("abs2")
        s._eta_uf.union("abs1", "abs2")
        result = s._resolve_type("int")
        assert result == s._eta_uf.find("abs1")

    def test_abstraction_not_in_uf(self) -> None:
        s = SPPF()
        s._eta_abstractions["int"] = "abs_no_uf"
        assert s._resolve_type("int") == "abs_no_uf"


# ── SPPF residue tracking ───────────────────────────────────────────

class TestResidueTracking:
    def test_update_residue_none(self) -> None:
        s = SPPF()
        s.tau._assign(("sig",), (), 0)
        s._update_residue(0, None)
        assert 0 not in s._residue_sets or len(s._residue_sets[0]) == 0

    def test_merge_residue_sets(self) -> None:
        s = SPPF()
        s.tau._assign(("a",), (), 0)
        s.tau._assign(("b",), (), 1)
        s._residue_sets[0] = {"int"}
        s._residue_sets[1] = {"str"}
        s._merge_residue_sets(0, 1)
        assert "str" in s._residue_sets[0]

    def test_merge_residue_loser_empty(self) -> None:
        s = SPPF()
        s.tau._assign(("a",), (), 0)
        s.tau._assign(("b",), (), 1)
        s._residue_sets[0] = {"int"}
        s._merge_residue_sets(0, 1)
        assert s._residue_sets[0] == {"int"}


# ── SPPF recanon_structural_key ─────────────────────────────────────

class TestRecanonStructuralKey:
    def test_unchanged(self) -> None:
        s = SPPF()
        s.tau._assign(("sig",), (), 0)
        key = ("X", (0,))
        new_key, changed = s._recanon_structural_key(key)
        assert not changed
        assert new_key == key

    def test_changed(self) -> None:
        s = SPPF()
        a = s.tau._assign(("a",), (), 0)
        b = s.tau._assign(("b",), (), 1)
        s.tau.merge(a, b)
        canon = s.tau.canonical(a)
        non_canon = b if b != canon else a
        if non_canon != canon:
            key = ("X", (non_canon,))
            new_key, changed = s._recanon_structural_key(key)
            assert changed
            assert new_key == ("X", (canon,))


# ── SPPF summary coverage ───────────────────────────────────────────

class TestSPPFSummary:
    def test_summary_with_eta(self) -> None:
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        s._ingest_node("X", (), "bool", "k3", (), (), (), 2, "f")
        text = s.summary()
        assert "η first-order" in text
        assert "η higher-order" in text

    def test_summary_kappa_independence(self) -> None:
        s = SPPF()
        s._ingest_node("X", (("n", "a"),), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (("n", "a"),), "str", "k2", (), (), (), 1, "f")
        text = s.summary()
        assert "κ independence" in text

    def test_summary_cell_observations(self) -> None:
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        text = s.summary()
        assert "cell observations" in text

    def test_summary_informative_ghost_filter(self) -> None:
        """Force kappa_independent > S * 0.01 for 'informative' branch."""
        s = SPPF()
        # Need many nodes sharing sigma but different kappa
        for i in range(10):
            dep = f"type_{i}"
            ktag = f"k{i % 3}"
            s._ingest_node("X", (), dep, ktag, (), (), (), i, "f")
        text = s.summary()
        assert "ghost filter" in text

    def test_summary_with_eta_names(self) -> None:
        """Cover the eta_roots computation when eta_names is non-empty."""
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        text = s.summary()
        assert "abstractions" in text

    def test_summary_empty_cell_obs_level(self) -> None:
        """A cell obs level with empty cells dict → skipped."""
        s = SPPF()
        s._ingest_node("X", (), "t", "k", (), (), (), 0, "f")
        s._cell_obs[5]  # create empty level
        text = s.summary()
        assert "SPPF:" in text

    def test_summary_cell_level_names(self) -> None:
        """Exercise all cell_names keys."""
        s = SPPF()
        s._ingest_node("X", (), "t", "k", (), (), (), 0, "f")
        for level in range(5):
            s._cell_obs[level]["test"] = 1
        text = s.summary()
        assert "node" in text
        assert "τ-class" in text


# ── Integration: full η cascade through _ingest_node ─────────────────

class TestIntegrationCascade:
    def test_deep_cascade(self) -> None:
        """Build a multi-level tree that triggers cascading merges."""
        s = SPPF()
        # Leaves
        _, la, _, _ = s._ingest_node("L", (), "a", "l", (), (), (), 0, "f")
        _, lb, _, _ = s._ingest_node("L", (), "b", "l", (), (), (), 1, "f")
        # la and lb merged (η at leaf level)

        # Mid-level referencing la
        _, ma, _, _ = s._ingest_node("M", (), "x", "m", (), (la,), (), 2, "f")
        _, mb, _, _ = s._ingest_node("M", (), "y", "m", (), (la,), (), 3, "f")
        # ma and mb merged (η at mid level)

        # Top-level referencing ma
        s._ingest_node("T", (), "p", "t", (), (ma,), (), 4, "f")
        s._ingest_node("T", (), "q", "t", (), (ma,), (), 5, "f")

        assert s.node_count == 6

    def test_parallel_cascade(self) -> None:
        """Two parallel sub-trees that interact via cascade."""
        s = SPPF()
        # Group A
        _, ca, _, _ = s._ingest_node("C", (), "c1", "cl", (), (), (), 0, "f")
        s._ingest_node("P", (), "int", "ka", (), (ca,), (), 1, "f")
        s._ingest_node("P", (), "str", "kb", (), (ca,), (), 2, "f")

        # Group B
        _, cb, _, _ = s._ingest_node("C", (), "c2", "cl", (), (), (), 3, "f")
        s._ingest_node("P", (), "int", "kc", (), (cb,), (), 4, "f")
        s._ingest_node("P", (), "str", "kd", (), (cb,), (), 5, "f")

        # Group C — triggers merge of c1 and c2 at leaf level
        s._ingest_node("C", (), "c3", "cl", (), (), (), 6, "f")

        assert s.node_count == 7

    def test_factorize_complex(self) -> None:
        """Use factorize on source with many repeated patterns."""
        from cstz import factorize
        code = """
def add(x, y):
    return x + y

def sub(x, y):
    return x - y

def mul(x, y):
    return x * y

a = add(1, 2)
b = sub(3, 4)
c = mul(5, 6)
d = add(a, b)
e = sub(b, c)
"""
        sppf = factorize(code)
        assert sppf.node_count > 0
        text = sppf.summary()
        assert "η first-order" in text

    def test_ackermann_prime_factors(self) -> None:
        """Ackermann function + prime factorization: structurally
        rich Python with deep recursion patterns and repeated
        arithmetic/control structures to exercise η-cascades."""
        import ast
        from cstz import factorize
        code = """
def ackermann(m, n):
    if m == 0:
        return n + 1
    if n == 0:
        return ackermann(m - 1, 1)
    return ackermann(m - 1, ackermann(m, n - 1))

def prime_factors(n):
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n = n // d
        d = d + 1
    if n > 1:
        factors.append(n)
    return factors

def collatz(n):
    steps = []
    while n != 1:
        steps.append(n)
        if n % 2 == 0:
            n = n // 2
        else:
            n = 3 * n + 1
    steps.append(1)
    return steps

def gcd(a, b):
    while b != 0:
        a, b = b, a % b
    return a

def lcm(a, b):
    return a * b // gcd(a, b)

results = []
for i in range(2, 20):
    f = prime_factors(i)
    results.append(f)
    if len(f) == 1:
        results.append(collatz(i))

pairs = []
for i in range(2, 10):
    for j in range(2, 10):
        g = gcd(i, j)
        l = lcm(i, j)
        pairs.append((i, j, g, l))

a0 = ackermann(0, 0)
a1 = ackermann(1, 1)
a2 = ackermann(2, 2)
a3 = ackermann(3, 3)
total = a0 + a1 + a2 + a3
"""
        sppf = factorize(ast.parse(code))
        assert sppf.node_count > 50
        text = sppf.summary()
        assert sppf._eta_count >= 1
        _ = sppf.cleavage()
        _ = sppf.natural_transformations("sigma")

    def test_fixed_point_after_ingest(self) -> None:
        """R7: After ingestion the τ-partition is at a fixed point.

        Re-resolving all structural key variants must find no two variants
        in the same key whose resolved dep-type is identical but whose
        canonical τ-ids differ.  A failure would indicate that the cascade
        stopped short of the fixed point promised by spec postulate P2.
        """
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        s._ingest_node("X", (), "bool", "k3", (), (), (), 2, "f")
        leaf_tau = s.tau.canonical(s.nodes[0]['tau'])
        s._ingest_node("P", (), "dep_a", "p1", (), (leaf_tau,), (), 3, "f")
        s._ingest_node("P", (), "dep_b", "p2", (), (leaf_tau,), (), 4, "f")

        for key, variants in s._tau_structural.items():
            seen: dict[object, int] = {}
            for dep_type, tid in variants.items():
                resolved = s._resolve_type(dep_type)
                canon = s.tau.canonical(tid)
                if resolved in seen:
                    assert seen[resolved] == canon, (
                        f"Fixed-point violation at key {key!r}: "
                        f"dep-type {dep_type!r} resolves to {resolved!r} but "
                        f"canonical τ-ids {seen[resolved]} and {canon} differ"
                    )
                seen[resolved] = canon


# ── Pathological inputs (co-located with core tests) ────────────────

def _pathological_partition(s: SPPF) -> set[frozenset[int]]:
    """Extract the τ-partition as sets of stable node IDs.

    We use each node's source `line` field rather than insertion index,
    so partitions can be compared across different ingestion orders.
    """
    groups: dict[int, set[int]] = {}
    for node in s.nodes:
        canon = s.tau.canonical(node["tau"])
        groups.setdefault(canon, set()).add(node["line"])
    return {frozenset(v) for v in groups.values()}


def _pathological_fixed_point_violations(s: SPPF) -> list[str]:
    """Return violations where a resolved dep_type maps to >1 canonical τ."""
    violations: list[str] = []
    for struct_key, variants in list(s._tau_structural.items()):
        resolved_to_tid: dict[str | None, set[int]] = {}
        for dt, tid in variants.items():
            resolved = s._resolve_type(dt)
            canon = s.tau.canonical(tid)
            resolved_to_tid.setdefault(resolved, set()).add(canon)
        for resolved, canons in resolved_to_tid.items():
            if len(canons) > 1:
                violations.append(
                    f"key={struct_key}, resolved={resolved!r}, distinct_canons={canons}"
                )
    return violations


class TestPathologicalFixedPoint:
    def test_pathological_three_way_eta_fixed_point(self) -> None:
        s = SPPF()
        s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
        s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
        s._ingest_node("X", (), "bool", "k3", (), (), (), 2, "f")
        assert _pathological_fixed_point_violations(s) == []

    def test_pathological_diamond_cascade_fixed_point(self) -> None:
        s = SPPF()
        _, cl1, _, _ = s._ingest_node("CL", (), "a", "leaf", (), (), (), 0, "f")
        s._ingest_node("CL", (), "b", "leaf", (), (), (), 1, "f")
        cl = s.tau.canonical(cl1)

        _, cr1, _, _ = s._ingest_node("CR", (), "x", "leaf", (), (), (), 2, "f")
        s._ingest_node("CR", (), "y", "leaf", (), (), (), 3, "f")
        cr = s.tau.canonical(cr1)

        s._ingest_node("P", (), "int", "k1", (), (cl, cr), (), 4, "f")
        s._ingest_node("P", (), "str", "k2", (), (cl, cr), (), 5, "f")
        assert _pathological_fixed_point_violations(s) == []

    def test_pathological_deep_chain_fixed_point(self) -> None:
        s = SPPF()
        line = 0

        def ingest(ast: str, dep: str, ktag: str,
                   children: tuple[int, ...] = ()):
            nonlocal line
            result = s._ingest_node(ast, (), dep, ktag, (), children, (), line, "f")
            line += 1
            return result

        _, t0a, _, _ = ingest("L0", "a", "k")
        ingest("L0", "b", "k")
        c0 = s.tau.canonical(t0a)

        _, t1a, _, _ = ingest("L1", "c", "k", (c0,))
        ingest("L1", "d", "k", (c0,))
        c1 = s.tau.canonical(t1a)

        _, t2a, _, _ = ingest("L2", "e", "k", (c1,))
        ingest("L2", "f", "k", (c1,))
        c2 = s.tau.canonical(t2a)

        ingest("L3", "g", "k", (c2,))
        ingest("L3", "h", "k", (c2,))

        assert _pathological_fixed_point_violations(s) == []


class TestPathologicalOrderIndependence:
    @staticmethod
    def _build(order: list[int]) -> SPPF:
        specs = [
            ("X", "int", "k1"),
            ("X", "str", "k2"),
            ("X", "bool", "k3"),
            ("Y", "int", "k4"),
            ("Y", "str", "k5"),
        ]
        s = SPPF()
        for idx in order:
            ast, dep, ktag = specs[idx]
            s._ingest_node(ast, (), dep, ktag, (), (), (), idx, "f")
        return s

    def test_pathological_forward_vs_reverse(self) -> None:
        assert _pathological_partition(self._build([0, 1, 2, 3, 4])) == (
            _pathological_partition(self._build([4, 3, 2, 1, 0]))
        )

    def test_pathological_children_then_parents_vs_mixed(self) -> None:
        s_a = SPPF()
        _, ca1, _, _ = s_a._ingest_node("C", (), "a", "leaf", (), (), (), 0, "f")
        s_a._ingest_node("C", (), "b", "leaf", (), (), (), 1, "f")
        c_canon_a = s_a.tau.canonical(ca1)
        s_a._ingest_node("P", (), "int", "k1", (), (c_canon_a,), (), 2, "f")
        s_a._ingest_node("P", (), "str", "k2", (), (c_canon_a,), (), 3, "f")

        s_b = SPPF()
        _, cb1, _, _ = s_b._ingest_node("C", (), "a", "leaf", (), (), (), 0, "f")
        s_b._ingest_node("P", (), "int", "k1", (), (s_b.tau.canonical(cb1),), (), 2, "f")
        s_b._ingest_node("C", (), "b", "leaf", (), (), (), 1, "f")
        s_b._ingest_node("P", (), "str", "k2", (), (s_b.tau.canonical(cb1),), (), 3, "f")

        assert _pathological_partition(s_a) == _pathological_partition(s_b)


class TestPathologicalR2EtaSquaredOrdering:
    def test_pathological_eta_squared_with_preexisting_abstractions(self) -> None:
        s = SPPF()
        line = 0

        def ingest(ast: str, dep: str, ktag: str,
                   child_taus: tuple[int, ...] = ()):
            nonlocal line
            r = s._ingest_node(ast, (), dep, ktag, (), child_taus, (), line, "f")
            line += 1
            return r

        _, c1, _, _ = ingest("C", "ct1", "cl")
        _, c2a, _, _ = ingest("D", "d1", "dl")
        ingest("D", "d2", "dl")
        c2 = s.tau.canonical(c2a)

        ingest("P", "alpha", "pa", (c1,))
        ingest("P", "beta", "pb", (c1,))
        ingest("P", "alpha", "pa", (c2,))
        ingest("P", "beta", "pb", (c2,))

        s._merge_residue_sets(c2, c1)
        s.tau.merge(c2, c1)
        s._cascade_eta({c1, c2}, line)

        assert _pathological_fixed_point_violations(s) == []


class TestPathologicalDeepCascade:
    def test_pathological_cascade_depth_6(self) -> None:
        s = SPPF()
        line = 0

        def ingest(ast: str, dep: str, ktag: str,
                   child_taus: tuple[int, ...] = ()):
            nonlocal line
            r = s._ingest_node(ast, (), dep, ktag, (), child_taus, (), line, "f")
            line += 1
            return r

        prev_canon: int | None = None
        for depth in range(6):
            children = (prev_canon,) if prev_canon is not None else ()
            _, ta, _, _ = ingest(f"L{depth}", f"dep_{depth}_a", "k", children)
            ingest(f"L{depth}", f"dep_{depth}_b", "k", children)
            prev_canon = s.tau.canonical(ta)

        assert _pathological_fixed_point_violations(s) == []

    def test_pathological_wide_fan_fixed_point(self) -> None:
        s = SPPF()
        line = 0

        def ingest(ast: str, dep: str, ktag: str,
                   child_taus: tuple[int, ...] = ()):
            nonlocal line
            r = s._ingest_node(ast, (), dep, ktag, (), child_taus, (), line, "f")
            line += 1
            return r

        _, c1, _, _ = ingest("C", "ca", "cl")
        ingest("C", "cb", "cl")
        c = s.tau.canonical(c1)

        for i in range(10):
            for dep in ["alpha", "beta", "gamma"]:
                ingest(f"P{i}", dep, f"k{i}", (c,))

        assert _pathological_fixed_point_violations(s) == []


class TestPathologicalR1Correction:
    def test_pathological_shared_tid_bridges_keys(self) -> None:
        s = SPPF()
        tid_a = s.tau._assign(("ta",), (), 0)
        tid_b = s.tau._assign(("tb",), (), 1)
        tid_c = s.tau._assign(("tc",), (), 2)
        for i in range(3):
            s.nodes.append(
                {
                    "ast_type": "X",
                    "params": (),
                    "dep_type": f"d{i}",
                    "dep_type_raw": f"d{i}",
                    "kappa_tag": f"k{i}",
                    "sigma": 0,
                    "tau": i,
                    "kappa": 0,
                    "line": i,
                    "file": "f",
                }
            )

        key_1: tuple[str, tuple[int, ...]] = ("P", ())
        key_2: tuple[str, tuple[int, ...]] = ("Q", ())

        s._tau_structural[key_1] = {"v1": tid_a, "v2": tid_b}
        s._tau_structural[key_2] = {"v2": tid_b, "v3": tid_c}
        s._tau_structural_by_variant["v1"] = {key_1}
        s._tau_structural_by_variant["v2"] = {key_1, key_2}
        s._tau_structural_by_variant["v3"] = {key_2}

        s._eta_abstractions["v1"] = "unified"
        s._eta_abstractions["v2"] = "unified"
        s._eta_abstractions["v3"] = "unified"
        s._eta_uf.make("unified")

        s._cascade_abstraction_merge({"v1", "v2", "v3", "unified"}, 0)

        assert s.tau.canonical(tid_a) == s.tau.canonical(tid_b)
        assert s.tau.canonical(tid_b) == s.tau.canonical(tid_c)
