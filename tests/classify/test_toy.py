"""Tests for cstz.classify.toy — toy binary-tree classifier."""

import pytest
from cstz.classify.adapter import emit_patch
from cstz.classify.toy import (
    ToyNode, make_toy_registry, ToyBinaryClassifier, toy_children,
)
from cstz.classify.walker import walk
from cstz.framework import ORDERED_TAU
from cstz.observe import ObservationState, Patch


# ---------------------------------------------------------------------------
# Tree fixtures
# ---------------------------------------------------------------------------


def _leaf(v):
    return ToyNode(kind="leaf", value=v)


def _branch(l, r):
    return ToyNode(kind="branch", left=l, right=r)


# ---------------------------------------------------------------------------
# Registry tests
# ---------------------------------------------------------------------------


class TestRegistry:
    def test_seven_discriminators(self):
        reg = make_toy_registry()
        assert len(reg) == 7

    def test_names(self):
        reg = make_toy_registry()
        names = [d.name for d in reg.all()]
        assert set(names) == {
            "is_leaf", "is_branch", "value_even", "value_odd",
            "has_left_leaf", "has_right_leaf", "symmetric",
        }

    def test_ids_are_one_hot(self):
        reg = make_toy_registry()
        mask = 0
        for d in reg.all():
            assert d.id & mask == 0  # no overlap
            mask |= d.id
        assert mask == 0b1111111  # 7 bits set


# ---------------------------------------------------------------------------
# Classifier tests
# ---------------------------------------------------------------------------


class TestToyChildren:
    def test_leaf_has_no_children(self):
        assert toy_children(_leaf(5)) == ()

    def test_branch_has_two_children(self):
        l = _leaf(1)
        r = _leaf(2)
        children = toy_children(_branch(l, r))
        assert children == (("left", l), ("right", r))


class TestToyClassifier:
    def _make(self):
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(
            reg, tuple(d.id for d in reg.all())
        )
        return reg, classifier

    def test_leaf_even(self):
        reg, classifier = self._make()
        c = classifier.classify(_leaf(4))
        expected = (reg.get_by_name("is_leaf").id
                    | reg.get_by_name("value_even").id)
        assert c.tau == expected
        assert c.shape.arity == 0

    def test_leaf_odd(self):
        reg, classifier = self._make()
        c = classifier.classify(_leaf(3))
        expected = (reg.get_by_name("is_leaf").id
                    | reg.get_by_name("value_odd").id)
        assert c.tau == expected

    def test_branch_two_leaves(self):
        reg, classifier = self._make()
        node = _branch(_leaf(1), _leaf(2))
        c = classifier.classify(node)
        expected = (reg.get_by_name("is_branch").id
                    | reg.get_by_name("has_left_leaf").id
                    | reg.get_by_name("has_right_leaf").id
                    | reg.get_by_name("symmetric").id)
        assert c.tau == expected
        assert c.shape.arity == 2
        assert c.shape.roles == ("left", "right")

    def test_asymmetric_branch(self):
        reg, classifier = self._make()
        node = _branch(_leaf(1), _branch(_leaf(2), _leaf(3)))
        c = classifier.classify(node)
        # is_branch, has_left_leaf (not right), not symmetric
        assert c.tau & reg.get_by_name("is_branch").id
        assert c.tau & reg.get_by_name("has_left_leaf").id
        assert not (c.tau & reg.get_by_name("has_right_leaf").id)
        assert not (c.tau & reg.get_by_name("symmetric").id)


# ---------------------------------------------------------------------------
# End-to-end pipeline tests
# ---------------------------------------------------------------------------


class TestPipeline:
    def _make(self):
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(
            reg, tuple(d.id for d in reg.all())
        )
        return reg, classifier

    def test_single_leaf_observations(self):
        reg, classifier = self._make()
        tree = _leaf(4)
        patch = Patch()
        emit_patch(walk(tree, classifier, toy_children), patch)
        # is_leaf + value_even fire → 2 observations
        assert len(patch.observations) == 2

    def test_three_node_tree_observations(self):
        reg, classifier = self._make()
        tree = _branch(_leaf(1), _leaf(2))
        patch = Patch()
        emit_patch(walk(tree, classifier, toy_children), patch)
        # Root: is_branch + has_left_leaf + has_right_leaf + symmetric = 4
        # Left leaf (v=1): is_leaf + value_odd = 2
        # Right leaf (v=2): is_leaf + value_even = 2
        # Total: 8
        assert len(patch.observations) == 8

    def test_observations_are_tau_only(self):
        reg, classifier = self._make()
        tree = _branch(_leaf(1), _leaf(2))
        patch = Patch()
        emit_patch(walk(tree, classifier, toy_children), patch)
        for obs in patch.observations:
            assert obs.result == ORDERED_TAU

    def test_merge_into_state(self):
        reg, classifier = self._make()
        tree = _branch(_leaf(1), _leaf(2))
        state = ObservationState(dim=len(reg))
        patch = state.new_patch()
        emit_patch(walk(tree, classifier, toy_children), patch)

        # 3 nodes visited → 3 distinct z-paths
        assert len(state.all_elements()) == 3

    def test_regime_matches_fired_discriminators(self):
        reg, classifier = self._make()
        # Tree that fires every discriminator somewhere
        tree = _branch(_leaf(2), _leaf(3))
        patch = Patch()
        emit_patch(walk(tree, classifier, toy_children), patch)
        # All 7 discriminators fire at least once
        assert len(patch.regime) == 7
        fired = set(patch.regime)
        for d in reg.all():
            assert d.id in fired


# ---------------------------------------------------------------------------
# Yoneda sanity gate
# ---------------------------------------------------------------------------


class TestYonedaSanityGate:
    """Phase 1 gate: two trees with different structure but identical
    τ per node remain distinguishable by z-path; two nodes with
    different z-path but identical τ become equivalent under
    τ-projection.
    """

    def test_different_structure_distinguishable_by_zpath(self):
        """Branch(L(2), L(3)) vs Branch(L(3), L(2)) — same τ-multiset
        at each depth, but z-paths differ at the leaves."""
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(
            reg, tuple(d.id for d in reg.all())
        )

        t1 = _branch(_leaf(2), _leaf(3))  # even-left, odd-right
        t2 = _branch(_leaf(3), _leaf(2))  # odd-left, even-right

        p1 = Patch()
        p2 = Patch()
        emit_patch(walk(t1, classifier, toy_children), p1)
        emit_patch(walk(t2, classifier, toy_children), p2)

        # The LEFT child in t1 is value_even; in t2 it's value_odd.
        # z-path 0b10 (left child) has different τ accumulation.
        left_child_zp = 0b10
        def profile_at(patch, zp):
            return sum(
                o.discriminator for o in patch.observations
                if o.element == zp
            )
        assert profile_at(p1, left_child_zp) != profile_at(p2, left_child_zp)

    def test_identical_tau_equivalent_under_profile(self):
        """Two leaves with the same value at different z-paths have
        identical τ per node.  Under τ-projection (ignoring z-path),
        they are equivalent."""
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(
            reg, tuple(d.id for d in reg.all())
        )
        # Two leaves both with value=4: both fire (is_leaf, value_even)
        c1 = classifier.classify(_leaf(4))
        c2 = classifier.classify(_leaf(4))
        assert c1.tau == c2.tau
        assert c1 == c2  # same Classified

    def test_z_paths_are_injective_in_walk(self):
        """The walker produces unique z-paths per node position."""
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(
            reg, tuple(d.id for d in reg.all())
        )
        tree = _branch(
            _branch(_leaf(1), _leaf(2)),
            _branch(_leaf(3), _leaf(4)),
        )
        results = list(walk(tree, classifier, toy_children))
        zpaths = [zp for zp, _ in results]
        assert len(set(zpaths)) == len(zpaths), "z-paths must be unique"
