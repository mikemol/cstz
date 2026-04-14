"""Tests for cstz.classify.bytes — byte segment tree + Morton keys.

Phase 2 gate checks:
  A. Key disjointness — leaf keys are odd; Nil/Seg keys are even
  B. Key uniqueness   — leaf keys unique (one per byte index)
  C. Key stability    — reconstruction preserves all keys
  D. Overlapping classifiers — shared registry gives comparable τ
  E. Merge commutativity — patch order does not affect profile
"""

import pytest
from cstz.classify.adapter import emit_patch
from cstz.classify.base import Classifier, ShapeWitness
from cstz.classify.bytes import (
    ByteNil, ByteLeaf, ByteSeg, ByteClassifier,
    bytes_to_tree, byte_children, byte_key, morton2,
    make_ascii_registry, make_bitwise_registry, make_segment_registry,
)
from cstz.classify.registry import DiscriminatorRegistry
from cstz.classify.walker import walk
from cstz.framework import ORDERED_TAU
from cstz.observe import ObservationState, Patch


# ---------------------------------------------------------------------------
# Morton encoding
# ---------------------------------------------------------------------------


class TestMorton:
    def test_zero_zero(self):
        assert morton2(0, 0) == 0

    def test_one_zero(self):
        # a=1 (0b1) bit at position 0 → result bit 0
        assert morton2(1, 0) == 0b01

    def test_zero_one(self):
        # b=1 (0b1) bit at position 0 → result bit 1
        assert morton2(0, 1) == 0b10

    def test_one_one(self):
        # both bit 0 → result bits 0 and 1
        assert morton2(1, 1) == 0b11

    def test_interleaving_pattern(self):
        # a=0b11 (bits at 0,1), b=0b00 → result bits at 0,2
        assert morton2(0b11, 0) == 0b0101
        # a=0b00, b=0b11 → result bits at 1,3
        assert morton2(0, 0b11) == 0b1010

    def test_pure(self):
        for a in range(8):
            for b in range(8):
                assert morton2(a, b) == morton2(a, b)

    def test_injective(self):
        seen = set()
        for a in range(16):
            for b in range(16):
                k = morton2(a, b)
                assert k not in seen, f"collision at ({a}, {b}) = {k}"
                seen.add(k)

    def test_negative_rejected(self):
        with pytest.raises(ValueError):
            morton2(-1, 0)
        with pytest.raises(ValueError):
            morton2(0, -1)


# ---------------------------------------------------------------------------
# Tree construction
# ---------------------------------------------------------------------------


class TestBytesToTree:
    def test_empty(self):
        assert bytes_to_tree(b"") == ByteNil()

    def test_single_byte(self):
        tree = bytes_to_tree(b"A")
        assert tree == ByteLeaf(value=0x41, index=0)

    def test_two_bytes(self):
        tree = bytes_to_tree(b"AB")
        assert isinstance(tree, ByteSeg)
        assert tree.lo == 0 and tree.hi == 2
        assert tree.left == ByteLeaf(0x41, 0)
        assert tree.right == ByteLeaf(0x42, 1)

    def test_four_bytes_balanced(self):
        tree = bytes_to_tree(b"ABCD")
        assert isinstance(tree, ByteSeg)
        assert tree.lo == 0 and tree.hi == 4
        # Left half: AB, right half: CD
        assert isinstance(tree.left, ByteSeg)
        assert tree.left.lo == 0 and tree.left.hi == 2
        assert isinstance(tree.right, ByteSeg)
        assert tree.right.lo == 2 and tree.right.hi == 4

    def test_deterministic(self):
        """Same input → same tree (reconstruction stability)."""
        t1 = bytes_to_tree(b"Hello, World!")
        t2 = bytes_to_tree(b"Hello, World!")
        assert t1 == t2


# ---------------------------------------------------------------------------
# Children function
# ---------------------------------------------------------------------------


class TestByteChildren:
    def test_nil_no_children(self):
        assert byte_children(ByteNil()) == ()

    def test_leaf_no_children(self):
        assert byte_children(ByteLeaf(0x41, 0)) == ()

    def test_seg_two_children(self):
        l = ByteLeaf(0x41, 0)
        r = ByteLeaf(0x42, 1)
        seg = ByteSeg(lo=0, hi=2, left=l, right=r)
        assert byte_children(seg) == (("left", l), ("right", r))


# ---------------------------------------------------------------------------
# Classifier shape_of
# ---------------------------------------------------------------------------


class TestShapeOf:
    def test_nil_arity_0(self):
        c = ByteClassifier(DiscriminatorRegistry(), ())
        s = c.shape_of(ByteNil())
        assert s.arity == 0
        assert s.roles == ()

    def test_leaf_arity_0(self):
        c = ByteClassifier(DiscriminatorRegistry(), ())
        s = c.shape_of(ByteLeaf(0, 0))
        assert s.arity == 0
        assert s.roles == ()

    def test_seg_arity_2(self):
        c = ByteClassifier(DiscriminatorRegistry(), ())
        seg = ByteSeg(0, 2, ByteLeaf(0, 0), ByteLeaf(0, 1))
        s = c.shape_of(seg)
        assert s.arity == 2
        assert s.roles == ("left", "right")

    def test_no_context_leak(self):
        """Arity depends only on the node's type, never on surrounding
        structure.  This is the Phase 2 gate: no 'last byte' check."""
        c = ByteClassifier(DiscriminatorRegistry(), ())
        # The same ByteLeaf returns arity 0 regardless of where it sits
        leaf = ByteLeaf(0x41, 42)
        s1 = c.shape_of(leaf)  # "standalone"
        # Place the same leaf inside a segment
        seg = ByteSeg(42, 43, leaf, ByteLeaf(0, 0))
        s2 = c.shape_of(leaf)  # child of a segment
        assert s1 == s2


# ---------------------------------------------------------------------------
# Key discipline — the three structural gates
# ---------------------------------------------------------------------------


class TestKeyDisjointness:
    """Gate A: leaf keys odd; Nil/Seg keys even."""

    def test_nil_key_is_zero(self):
        assert byte_key(ByteNil()) == 0

    def test_nil_key_is_even(self):
        assert byte_key(ByteNil()) % 2 == 0

    def test_leaf_keys_are_odd(self):
        for index in range(20):
            k = byte_key(ByteLeaf(value=0x41, index=index))
            assert k % 2 == 1, f"leaf at index {index} has even key {k}"

    def test_seg_keys_are_even(self):
        for lo in range(10):
            for hi in range(lo + 1, lo + 8):
                k = byte_key(ByteSeg(lo=lo, hi=hi,
                                     left=ByteLeaf(0, lo),
                                     right=ByteLeaf(0, hi - 1)))
                assert k % 2 == 0, f"seg ({lo},{hi}) has odd key {k}"

    def test_disjoint_leaf_vs_seg(self):
        """No leaf key equals any segment key (low-bit tag disjointness)."""
        leaf_keys = {byte_key(ByteLeaf(0, i)) for i in range(16)}
        seg_keys = set()
        for lo in range(16):
            for hi in range(lo + 1, 17):
                seg_keys.add(byte_key(
                    ByteSeg(lo=lo, hi=hi,
                            left=ByteLeaf(0, lo),
                            right=ByteLeaf(0, hi - 1))))
        assert leaf_keys.isdisjoint(seg_keys)


class TestKeyUniqueness:
    """Gate B: leaf keys unique per byte index."""

    def test_leaf_keys_unique_small(self):
        keys = {byte_key(ByteLeaf(value=0x41, index=i)) for i in range(100)}
        assert len(keys) == 100  # all distinct

    def test_leaf_keys_independent_of_value(self):
        """Byte VALUE does not affect the key; only INDEX does."""
        for index in range(20):
            keys = {byte_key(ByteLeaf(value=v, index=index)) for v in range(256)}
            assert len(keys) == 1  # all 256 values share the same key at that index

    def test_seg_keys_unique_across_ranges(self):
        """Different (lo, hi) produce different keys."""
        pairs = [(0, 4), (0, 8), (4, 8), (1, 5), (2, 6)]
        keys = {byte_key(ByteSeg(lo, hi,
                                  ByteLeaf(0, lo),
                                  ByteLeaf(0, hi - 1)))
                for lo, hi in pairs}
        assert len(keys) == len(pairs)


class TestKeyStability:
    """Gate C: reconstruction preserves keys."""

    def test_leaf_key_stable(self):
        """Same index → same key, always."""
        t1 = bytes_to_tree(b"Hello")
        t2 = bytes_to_tree(b"Hello")
        # Collect leaf keys from both trees
        def collect_leaf_keys(node):
            if isinstance(node, ByteLeaf):
                return {node.index: byte_key(node)}
            if isinstance(node, ByteSeg):
                out = {}
                out.update(collect_leaf_keys(node.left))
                out.update(collect_leaf_keys(node.right))
                return out
            return {}
        assert collect_leaf_keys(t1) == collect_leaf_keys(t2)

    def test_leaf_key_independent_of_content_size(self):
        """A byte at index=2 in 'ABCD' has the same leaf key as
        a byte at index=2 in 'ABCDEFGH'."""
        t_short = bytes_to_tree(b"ABCD")
        t_long = bytes_to_tree(b"ABCDEFGH")

        def leaf_at(node, idx):
            if isinstance(node, ByteLeaf):
                return node if node.index == idx else None
            if isinstance(node, ByteSeg):
                return leaf_at(node.left, idx) or leaf_at(node.right, idx)
            return None

        k_short = byte_key(leaf_at(t_short, 2))
        k_long = byte_key(leaf_at(t_long, 2))
        assert k_short == k_long


# ---------------------------------------------------------------------------
# Registry tests
# ---------------------------------------------------------------------------


class TestAsciiRegistry:
    def test_size(self):
        reg = make_ascii_registry()
        assert len(reg) == 8  # is_leaf + 7 ASCII categories

    def test_names(self):
        reg = make_ascii_registry()
        names = {d.name for d in reg.all()}
        assert names == {
            "is_leaf", "is_zero", "is_ascii", "is_letter",
            "is_digit", "is_whitespace", "is_control", "is_printable",
        }

    def test_discriminator_only_fires_on_leaf(self):
        reg = make_ascii_registry()
        # Nil and Seg never fire any discriminator
        for d in reg.all():
            assert d.fires(ByteNil()) is False
            assert d.fires(ByteSeg(0, 2, ByteLeaf(0, 0), ByteLeaf(0, 1))) is False


class TestBitwiseRegistry:
    def test_fresh(self):
        reg = make_bitwise_registry()
        assert len(reg) == 8

    def test_extend(self):
        """Passing an existing registry adds to it, preserving prior discriminators."""
        reg = make_ascii_registry()
        before = len(reg)
        result = make_bitwise_registry(reg)
        assert result is reg  # same instance
        assert len(reg) == before + 8

    def test_bit_independence(self):
        """bit_k discriminator fires iff bit k is set in the byte value."""
        reg = make_bitwise_registry()
        bits = [reg.get_by_name(f"bit_{i}") for i in range(8)]
        for value in (0x00, 0x01, 0xA5, 0xFF):
            leaf = ByteLeaf(value=value, index=0)
            for i, d in enumerate(bits):
                expected = bool(value & (1 << i))
                assert d.fires(leaf) is expected, \
                    f"value {value:#x}, bit {i}: expected {expected}"


class TestSegmentRegistry:
    def test_basic(self):
        reg = make_segment_registry()
        assert len(reg) == 5

    def test_extend(self):
        """Passing an existing registry adds to it."""
        reg = make_ascii_registry()
        before = len(reg)
        result = make_segment_registry(reg)
        assert result is reg
        assert len(reg) == before + 5

    def test_is_nil_on_non_nil(self):
        """is_nil fires only on ByteNil."""
        reg = make_segment_registry()
        d = reg.get_by_name("is_nil")
        assert d.fires(ByteNil()) is True
        assert d.fires(ByteLeaf(0x41, 0)) is False
        assert d.fires(ByteSeg(0, 2, ByteLeaf(0, 0), ByteLeaf(0, 1))) is False

    def test_seg_never_fires_on_leaf(self):
        reg = make_segment_registry()
        leaf = ByteLeaf(0x41, 0)
        for d in reg.all():
            if d.name not in ("is_nil",):
                result = d.fires(leaf)
                assert result is False, f"{d.name} fired on leaf"

    def test_seg_discriminators_on_non_seg(self):
        """Segment discriminators with `isinstance(n, ByteSeg) and pred(n)`
        must short-circuit False on non-Seg nodes without touching pred."""
        reg = make_segment_registry()
        for name in ("seg_singleton", "seg_len_even", "seg_len_power_of_two"):
            d = reg.get_by_name(name)
            assert d.fires(ByteNil()) is False
            assert d.fires(ByteLeaf(0x41, 0)) is False

    def test_seg_discriminators_both_branches(self):
        """Exercise each seg discriminator with both True and False pred
        outcomes on actual ByteSeg instances."""
        reg = make_segment_registry()
        # seg_singleton: True path
        singleton = ByteSeg(5, 6, ByteLeaf(0, 5), ByteLeaf(0, 5))
        assert reg.get_by_name("seg_singleton").fires(singleton) is True
        # seg_singleton: False path on bigger seg
        larger = ByteSeg(0, 4, ByteLeaf(0, 0), ByteLeaf(0, 3))
        assert reg.get_by_name("seg_singleton").fires(larger) is False
        # seg_len_even: True and False
        assert reg.get_by_name("seg_len_even").fires(larger) is True  # len=4
        odd_seg = ByteSeg(0, 3, ByteLeaf(0, 0), ByteLeaf(0, 2))
        assert reg.get_by_name("seg_len_even").fires(odd_seg) is False

    def test_seg_len_power_of_two(self):
        reg = make_segment_registry()
        d = reg.get_by_name("seg_len_power_of_two")
        for (lo, hi, expected) in [
            (0, 1, True), (0, 2, True), (0, 4, True), (0, 8, True),
            (0, 3, False), (0, 5, False), (2, 6, True), (0, 0, False),
        ]:
            seg = ByteSeg(lo=lo, hi=hi,
                          left=ByteLeaf(0, lo),
                          right=ByteLeaf(0, max(lo, hi - 1)))
            assert d.fires(seg) is expected, f"({lo},{hi}) expected {expected}"


# ---------------------------------------------------------------------------
# End-to-end pipeline
# ---------------------------------------------------------------------------


class TestPipeline:
    def test_single_byte_emits_observations(self):
        reg = make_ascii_registry()
        classifier = ByteClassifier(reg, tuple(d.id for d in reg.all()))
        tree = bytes_to_tree(b"A")

        patch = Patch()
        emit_patch(
            walk(tree, classifier, byte_children, key_fn=byte_key),
            patch,
        )
        # 'A' = 0x41: is_leaf, is_ascii, is_letter, is_printable = 4 fires
        assert len(patch.observations) == 4
        for obs in patch.observations:
            assert obs.result == ORDERED_TAU
            # key is leaf key for index 0: (0 << 1) | 1 = 1
            assert obs.element == 1

    def test_empty_stream_emits_nothing(self):
        reg = make_ascii_registry()
        classifier = ByteClassifier(reg, tuple(d.id for d in reg.all()))
        tree = bytes_to_tree(b"")  # ByteNil
        patch = Patch()
        emit_patch(walk(tree, classifier, byte_children, key_fn=byte_key),
                   patch)
        # Nil fires nothing → no observations
        assert patch.observations == []
        assert patch.regime == []

    def test_hello_world(self):
        reg = make_ascii_registry()
        classifier = ByteClassifier(reg, tuple(d.id for d in reg.all()))
        tree = bytes_to_tree(b"Hello, World!")
        patch = Patch()
        emit_patch(walk(tree, classifier, byte_children, key_fn=byte_key),
                   patch)

        # Leaf keys for each byte index:
        leaf_keys = {(i << 1) | 1 for i in range(13)}
        observed_elements = {o.element for o in patch.observations}
        # At least the 13 leaf keys appear (segments have even keys,
        # but segments fire no ASCII discriminators)
        assert leaf_keys.issubset(observed_elements)

    def test_observations_use_byte_key_not_walk_zpath(self):
        """The emitted element is byte_key(node), not the walker's depth zpath."""
        reg = make_ascii_registry()
        classifier = ByteClassifier(reg, tuple(d.id for d in reg.all()))
        # Two-byte stream: tree is Seg(Leaf(A,0), Leaf(B,1))
        # Walker zpaths would be: Seg=0b1, LeafA=0b10, LeafB=0b11
        # Byte keys are:          Seg=morton2(0,2)<<1, LeafA=1, LeafB=3
        tree = bytes_to_tree(b"AB")
        patch = Patch()
        emit_patch(walk(tree, classifier, byte_children, key_fn=byte_key),
                   patch)
        elements = {o.element for o in patch.observations}
        # Byte keys 1 (LeafA) and 3 (LeafB) must be present; walker
        # depth zpaths (2 and 3) — but 3 IS LeafB's byte key, and 2
        # would have been LeafA's walker zpath.  Check specifically:
        # LeafA's byte_key is 1, NOT 2, proving we used byte_key.
        assert 1 in elements
        assert 3 in elements


# ---------------------------------------------------------------------------
# Gate D: overlapping classifiers (shared registry)
# ---------------------------------------------------------------------------


class TestOverlappingClassifiers:
    """Two classifiers sharing one registry with overlapping
    discriminator_ids must agree on overlapping bits when classifying
    the same node."""

    def test_overlap_comparability(self):
        # Build a combined registry: ASCII + bitwise
        reg = make_ascii_registry()
        make_bitwise_registry(reg)  # extends in place

        # Classifier A: ASCII-only
        ascii_ids = tuple(reg.get_by_name(n).id for n in (
            "is_leaf", "is_ascii", "is_letter", "is_digit",
        ))
        A = ByteClassifier(reg, ascii_ids)

        # Classifier B: bitwise + is_leaf (overlap on is_leaf)
        bitwise_ids = tuple(reg.get_by_name(f"bit_{i}").id for i in range(8))
        is_leaf_id = reg.get_by_name("is_leaf").id
        B = ByteClassifier(reg, (is_leaf_id,) + bitwise_ids)

        overlap = is_leaf_id  # only shared discriminator

        nodes = [
            ByteLeaf(value=0x41, index=0),    # letter
            ByteLeaf(value=0x35, index=1),    # digit
            ByteLeaf(value=0x00, index=2),    # zero
            ByteLeaf(value=0xFF, index=3),    # high bits
            ByteNil(),
            ByteSeg(0, 2, ByteLeaf(0, 0), ByteLeaf(0, 1)),
        ]
        for n in nodes:
            ta = A.classify(n).tau & overlap
            tb = B.classify(n).tau & overlap
            assert ta == tb, f"overlap mismatch on {n}: A={ta} B={tb}"


# ---------------------------------------------------------------------------
# Gate E: merge commutativity
# ---------------------------------------------------------------------------


class TestMergeCommutativity:
    """Emitting the same two classifiers' patches into an
    ObservationState in either order produces identical profiles."""

    def test_ab_vs_ba(self):
        reg = make_ascii_registry()
        make_bitwise_registry(reg)
        ascii_ids = tuple(reg.get_by_name(n).id for n in (
            "is_leaf", "is_letter", "is_digit", "is_printable",
        ))
        bit_ids = tuple(reg.get_by_name(f"bit_{i}").id for i in range(8))
        A = ByteClassifier(reg, ascii_ids)
        B = ByteClassifier(reg, bit_ids)

        tree = bytes_to_tree(b"XYZ")

        # State 1: A then B
        s1 = ObservationState(dim=len(reg))
        p1a = s1.new_patch()
        emit_patch(walk(tree, A, byte_children, key_fn=byte_key), p1a)
        p1b = s1.new_patch()
        emit_patch(walk(tree, B, byte_children, key_fn=byte_key), p1b)

        # State 2: B then A
        s2 = ObservationState(dim=len(reg))
        p2b = s2.new_patch()
        emit_patch(walk(tree, B, byte_children, key_fn=byte_key), p2b)
        p2a = s2.new_patch()
        emit_patch(walk(tree, A, byte_children, key_fn=byte_key), p2a)

        # Profiles at every byte-key element must match
        for i in range(3):
            leaf_key = (i << 1) | 1
            assert s1.profile(leaf_key) == s2.profile(leaf_key), \
                f"profile mismatch at leaf index {i}"

    def test_silent_classifier_contributes_nothing(self):
        """A classifier with empty discriminator_ids doesn't affect the
        state no matter when it's merged (silence)."""
        reg = make_ascii_registry()
        real = ByteClassifier(reg, tuple(d.id for d in reg.all()))
        silent = ByteClassifier(reg, ())

        tree = bytes_to_tree(b"hello")

        s1 = ObservationState(dim=len(reg))
        p1 = s1.new_patch()
        emit_patch(walk(tree, real, byte_children, key_fn=byte_key), p1)
        p1_silent = s1.new_patch()
        emit_patch(walk(tree, silent, byte_children, key_fn=byte_key), p1_silent)

        s2 = ObservationState(dim=len(reg))
        p2 = s2.new_patch()
        emit_patch(walk(tree, real, byte_children, key_fn=byte_key), p2)

        # s1 has a silent patch; s2 doesn't.  But profiles are identical.
        for i in range(5):
            leaf_key = (i << 1) | 1
            assert s1.profile(leaf_key) == s2.profile(leaf_key)
