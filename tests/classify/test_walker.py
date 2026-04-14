"""Tests for cstz.classify.walker — traversal and zpath encoding."""

import pytest
from dataclasses import dataclass
from typing import Optional
from cstz.classify.base import Classified, ShapeWitness, Classifier
from cstz.classify.registry import DiscriminatorRegistry
from cstz.classify.walker import zpath, walk


# ---------------------------------------------------------------------------
# zpath encoding tests
# ---------------------------------------------------------------------------


class TestZpath:
    def test_root(self):
        """Root: depth 0 → 0b1 = 1."""
        assert zpath(0, 0) == 0b1

    def test_depth_1(self):
        assert zpath(0, 1) == 0b10  # left child
        assert zpath(1, 1) == 0b11  # right child

    def test_depth_2(self):
        assert zpath(0b00, 2) == 0b100  # LL
        assert zpath(0b01, 2) == 0b101  # LR
        assert zpath(0b10, 2) == 0b110  # RL
        assert zpath(0b11, 2) == 0b111  # RR

    def test_depth_3(self):
        # path [R, L, R] = 0b101 at depth 3 → sentinel | bits
        assert zpath(0b101, 3) == 0b1101

    def test_negative_depth_rejected(self):
        with pytest.raises(ValueError, match="depth"):
            zpath(0, -1)

    def test_bits_out_of_range_rejected(self):
        # At depth 2, bits can be 0..3; 4 is out of range
        with pytest.raises(ValueError, match="out of range"):
            zpath(4, 2)

    def test_negative_bits_rejected(self):
        with pytest.raises(ValueError, match="out of range"):
            zpath(-1, 1)

    def test_injective(self):
        """Distinct (bits, depth) pairs produce distinct zpaths."""
        seen = set()
        for depth in range(5):
            for bits in range(1 << depth if depth > 0 else 1):
                zp = zpath(bits, depth)
                assert zp not in seen
                seen.add(zp)


# ---------------------------------------------------------------------------
# Toy tree for walk tests
# ---------------------------------------------------------------------------


@dataclass
class TNode:
    kind: str  # "leaf" or "branch"
    value: int = 0
    left: Optional["TNode"] = None
    right: Optional["TNode"] = None


def tree_children(node):
    if node.kind == "leaf":
        return ()
    return (("left", node.left), ("right", node.right))


class TreeClassifier(Classifier):
    def shape_of(self, node):
        if node.kind == "leaf":
            return ShapeWitness(0, ())
        return ShapeWitness(2, ("left", "right"))


def _make_empty_classifier():
    reg = DiscriminatorRegistry()
    return TreeClassifier(reg, ()), reg


def _make_trivial_classifier():
    reg = DiscriminatorRegistry()
    is_leaf = reg.register("is_leaf", lambda n: n.kind == "leaf")
    is_branch = reg.register("is_branch", lambda n: n.kind == "branch")
    return TreeClassifier(reg, (is_leaf, is_branch)), reg


# ---------------------------------------------------------------------------
# walk() tests
# ---------------------------------------------------------------------------


class TestWalkSingleNode:
    def test_single_leaf(self):
        classifier, _ = _make_empty_classifier()
        leaf = TNode("leaf", value=1)
        results = list(walk(leaf, classifier, tree_children))
        assert len(results) == 1
        zp, classified = results[0]
        assert zp == 0b1  # root
        assert classified.shape.arity == 0

    def test_single_leaf_with_discriminators(self):
        classifier, reg = _make_trivial_classifier()
        is_leaf = reg.get_by_name("is_leaf").id
        leaf = TNode("leaf")
        [(zp, c)] = list(walk(leaf, classifier, tree_children))
        assert c.tau == is_leaf


class TestWalkBinaryTree:
    def _build(self):
        """Tree:       branch
                       /    \\
                    leaf    branch
                             /    \\
                          leaf   leaf
        """
        return TNode("branch",
                     left=TNode("leaf", value=1),
                     right=TNode("branch",
                                 left=TNode("leaf", value=2),
                                 right=TNode("leaf", value=3)))

    def test_preorder_count(self):
        classifier, _ = _make_trivial_classifier()
        results = list(walk(self._build(), classifier, tree_children))
        # 5 nodes total
        assert len(results) == 5

    def test_preorder_zpaths(self):
        classifier, _ = _make_trivial_classifier()
        results = list(walk(self._build(), classifier, tree_children))
        zpaths = [zp for zp, _ in results]
        # Preorder: root, LL, RR-root, RR-LL, RR-LR wait let me think.
        # Root (0b1), Left (0b10), Right (0b11), Right.Left (0b110), Right.Right (0b111)
        expected = [0b1, 0b10, 0b11, 0b110, 0b111]
        assert zpaths == expected

    def test_zpaths_unique(self):
        classifier, _ = _make_trivial_classifier()
        results = list(walk(self._build(), classifier, tree_children))
        zpaths = [zp for zp, _ in results]
        assert len(set(zpaths)) == len(zpaths)

    def test_discriminator_firings(self):
        classifier, reg = _make_trivial_classifier()
        is_leaf = reg.get_by_name("is_leaf").id
        is_branch = reg.get_by_name("is_branch").id
        results = list(walk(self._build(), classifier, tree_children))
        # Root is branch
        assert results[0][1].tau == is_branch
        # LL is leaf
        assert results[1][1].tau == is_leaf
        # Right is branch
        assert results[2][1].tau == is_branch


class TestWalkErrors:
    def test_arity_mismatch_rejected(self):
        """If shape.arity=2 but children_fn returns 0, error."""
        reg = DiscriminatorRegistry()

        class BrokenClassifier(Classifier):
            def shape_of(self, node):
                return ShapeWitness(2, ("l", "r"))  # claims binary

        classifier = BrokenClassifier(reg, ())
        leaf = TNode("leaf")
        # children_fn returns () for leaves but classifier claims arity 2
        with pytest.raises(ValueError, match="arity"):
            list(walk(leaf, classifier, tree_children))


class TestWalkMonotonicity:
    """M6 pre-verification: stopping early gives a prefix of full walk."""

    def test_prefix_consistency(self):
        """Taking first k yields is identical to stopping walk after k."""
        classifier, _ = _make_trivial_classifier()
        tree = TNode("branch",
                     left=TNode("leaf", value=1),
                     right=TNode("leaf", value=2))
        full = list(walk(tree, classifier, tree_children))
        partial = []
        for i, item in enumerate(walk(tree, classifier, tree_children)):
            partial.append(item)
            if i >= 1:
                break
        assert partial == full[:2]

    def test_yield_is_lazy(self):
        """Walk is a generator; infinite trees would not hang on construction."""
        import types
        classifier, _ = _make_trivial_classifier()
        leaf = TNode("leaf")
        gen = walk(leaf, classifier, tree_children)
        assert isinstance(gen, types.GeneratorType)
