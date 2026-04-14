"""Meta-tests M1-M6 — cross-cutting invariants of the classify layer.

These tests verify the contractual invariants from the plan, not
per-module behavior.  They are the load-bearing leverage checks:
violating any of them means the design is broken, not just buggy.

M1. Classifier commutativity    — shared registry semantics
M2. τ-invariance under traversal order — identity vs address
M3. Silence                     — operationalist axiom (τ=0 → nothing)
M4. Registry growth             — backward compatibility
M5. Classifier idempotence      — no hidden state
M6. Walker monotonicity         — no retroactive rewrites
"""

from __future__ import annotations

import pytest
from cstz.classify.adapter import emit_patch
from cstz.classify.base import Classifier, Classified, ShapeWitness
from cstz.classify.registry import DiscriminatorRegistry
from cstz.classify.toy import (
    ToyBinaryClassifier, ToyNode, make_toy_registry, toy_children,
)
from cstz.classify.walker import walk, zpath
from cstz.framework import ORDERED_TAU
from cstz.observe import ObservationState, Patch


def _leaf(v):
    return ToyNode(kind="leaf", value=v)


def _branch(l, r):
    return ToyNode(kind="branch", left=l, right=r)


# ---------------------------------------------------------------------------
# M1. Classifier commutativity — shared registry semantics
# ---------------------------------------------------------------------------


class TestM1Commutativity:
    """Two classifiers from the same registry with overlapping
    discriminator_ids must agree on the overlap."""

    def test_overlap_agreement(self):
        reg = make_toy_registry()
        is_leaf = reg.get_by_name("is_leaf").id
        is_branch = reg.get_by_name("is_branch").id
        value_even = reg.get_by_name("value_even").id
        value_odd = reg.get_by_name("value_odd").id

        # A: {is_leaf, is_branch, value_even}
        A = ToyBinaryClassifier(reg, (is_leaf, is_branch, value_even))
        # B: {is_branch, value_even, value_odd}
        B = ToyBinaryClassifier(reg, (is_branch, value_even, value_odd))

        overlap = is_branch | value_even

        nodes = [_leaf(2), _leaf(3), _branch(_leaf(1), _leaf(2)),
                 _branch(_leaf(4), _branch(_leaf(5), _leaf(6)))]
        for n in nodes:
            a = A.classify(n)
            b = B.classify(n)
            assert (a.tau & overlap) == (b.tau & overlap), \
                f"overlap disagreement on {n}: A={a.tau:#b} B={b.tau:#b}"

    def test_singleton_overlap(self):
        reg = make_toy_registry()
        ids = [d.id for d in reg.all()]

        # Two disjoint classifiers; no overlap → trivially agree on ∅
        A = ToyBinaryClassifier(reg, (ids[0], ids[1]))
        B = ToyBinaryClassifier(reg, (ids[2], ids[3]))

        overlap = 0  # no common discriminators
        for n in (_leaf(2), _branch(_leaf(1), _leaf(2))):
            assert (A.classify(n).tau & overlap) == (B.classify(n).tau & overlap)


# ---------------------------------------------------------------------------
# M2. τ-invariance under traversal order
# ---------------------------------------------------------------------------


class TestM2TauInvarianceUnderTraversal:
    """Reordering sibling traversal changes z-paths but must not
    change the multiset of τ-signatures."""

    def test_swapped_children_same_tau_multiset(self):
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(reg, tuple(d.id for d in reg.all()))

        t1 = _branch(_leaf(2), _leaf(3))
        t2 = _branch(_leaf(3), _leaf(2))

        taus1 = sorted(c.tau for _, c in walk(t1, classifier, toy_children))
        taus2 = sorted(c.tau for _, c in walk(t2, classifier, toy_children))
        # The multiset of τ-signatures is the same; only the z-path
        # assignments differ.
        assert taus1 == taus2


# ---------------------------------------------------------------------------
# M3. Silence test
# ---------------------------------------------------------------------------


class TestM3Silence:
    """τ=0 must leave zero trace in ObservationState.

    Operationalist axiom: τ=0 means silence, not falsehood.
    """

    def test_tau_zero_emits_nothing(self):
        patch = Patch()
        emit_patch([(0b1, Classified(tau=0, shape=ShapeWitness(0, ())))], patch)
        assert patch.observations == []
        assert patch.regime == []

    def test_silent_classifier_leaves_state_empty(self):
        """A classifier with empty discriminator_ids produces τ=0
        everywhere, leaving the state untouched."""
        reg = make_toy_registry()
        silent = ToyBinaryClassifier(reg, ())  # empty projection

        tree = _branch(_leaf(1), _leaf(2))
        state = ObservationState(dim=len(reg))
        patch = state.new_patch()
        emit_patch(walk(tree, silent, toy_children), patch)

        assert patch.observations == []
        assert patch.regime == []
        # state has a patch but it's empty
        assert state.all_elements() == set()

    def test_silence_partial(self):
        """If some nodes fire, others don't, only firing nodes leave
        observations."""
        reg = DiscriminatorRegistry()
        # Only fires on leaves with value == 7
        fire_id = reg.register("is_lucky", lambda n: n.kind == "leaf" and n.value == 7)
        classifier = ToyBinaryClassifier(reg, (fire_id,))

        tree = _branch(_leaf(1), _branch(_leaf(7), _leaf(2)))
        patch = Patch()
        emit_patch(walk(tree, classifier, toy_children), patch)
        # Only the value=7 leaf fires → one observation total
        assert len(patch.observations) == 1
        assert patch.observations[0].discriminator == fire_id


# ---------------------------------------------------------------------------
# M4. Registry growth — backward compatibility
# ---------------------------------------------------------------------------


class TestM4RegistryGrowth:
    """Adding new discriminators to a registry must not change the
    low-order bits of τ-signatures computed over pre-existing
    discriminators."""

    def test_old_bits_preserved_after_growth(self):
        # Seed registry with 3 discriminators
        reg = DiscriminatorRegistry()
        is_leaf = reg.register("is_leaf", lambda n: n.kind == "leaf")
        is_branch = reg.register("is_branch", lambda n: n.kind == "branch")
        value_even = reg.register(
            "value_even",
            lambda n: n.kind == "leaf" and n.value % 2 == 0,
        )
        C_small = ToyBinaryClassifier(reg, (is_leaf, is_branch, value_even))

        # Classify a node; capture τ
        n = _leaf(4)
        tau_before = C_small.classify(n).tau

        # Grow the registry with new discriminators
        reg.register("value_odd", lambda n: n.kind == "leaf" and n.value % 2 == 1)
        reg.register("has_left_leaf", lambda n: False)

        # Classify same node with same small classifier → same τ
        tau_after_small = C_small.classify(n).tau
        assert tau_after_small == tau_before, \
            "adding new discriminators changed τ of existing classifier"

        # Large classifier adds bits only in new positions
        ids = tuple(d.id for d in reg.all())
        C_large = ToyBinaryClassifier(reg, ids)
        tau_large = C_large.classify(n).tau

        # Low-order bits (is_leaf|is_branch|value_even) must match
        low_mask = is_leaf | is_branch | value_even
        assert (tau_large & low_mask) == (tau_before & low_mask)


# ---------------------------------------------------------------------------
# M5. Classifier idempotence
# ---------------------------------------------------------------------------


class TestM5Idempotence:
    """classify(node) is pure: calling it many times returns
    identical results."""

    def test_100_calls_identical(self):
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(reg, tuple(d.id for d in reg.all()))
        node = _branch(_leaf(4), _leaf(5))
        expected = classifier.classify(node)
        for _ in range(100):
            assert classifier.classify(node) == expected

    def test_idempotent_across_nodes(self):
        """Multiple nodes in varying orders give consistent results."""
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(reg, tuple(d.id for d in reg.all()))
        nodes = [_leaf(i) for i in range(10)]

        results1 = [classifier.classify(n) for n in nodes]
        results2 = [classifier.classify(n) for n in reversed(nodes)]
        # Reversing the input list doesn't change per-node results
        assert results1 == list(reversed(results2))


# ---------------------------------------------------------------------------
# M6. Walker monotonicity
# ---------------------------------------------------------------------------


class TestM6Monotonicity:
    """Extending a walk yields more (zpath, Classified) pairs but
    never modifies previously yielded ones."""

    def test_prefix_is_prefix(self):
        """Stopping after k items gives exactly the first k items of
        a full walk."""
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(reg, tuple(d.id for d in reg.all()))
        tree = _branch(
            _branch(_leaf(1), _leaf(2)),
            _branch(_leaf(3), _leaf(4)),
        )
        full = list(walk(tree, classifier, toy_children))
        for k in range(1, len(full) + 1):
            partial = []
            for i, item in enumerate(walk(tree, classifier, toy_children)):
                partial.append(item)
                if i >= k - 1:
                    break
            assert partial == full[:k]

    def test_two_walks_identical(self):
        """Walking the same tree twice produces identical sequences."""
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(reg, tuple(d.id for d in reg.all()))
        tree = _branch(_leaf(1), _branch(_leaf(2), _leaf(3)))
        w1 = list(walk(tree, classifier, toy_children))
        w2 = list(walk(tree, classifier, toy_children))
        assert w1 == w2

    def test_no_retroactive_modification(self):
        """Walking a larger tree that extends a smaller one preserves
        the smaller walk's emissions up to the extension point.

        We test by constructing a small tree and a large tree that is
        the small tree placed in the LEFT subtree of a new root.  The
        small tree's walk emissions (relative to its own root zpaths)
        correspond to shifted zpaths in the large walk, but the
        τ-signatures at corresponding positions must match.
        """
        reg = make_toy_registry()
        classifier = ToyBinaryClassifier(reg, tuple(d.id for d in reg.all()))

        small = _branch(_leaf(1), _leaf(2))
        small_walk = list(walk(small, classifier, toy_children))

        # Large tree: the small tree is the LEFT subtree of a new root
        large = _branch(small, _leaf(99))
        large_walk = list(walk(large, classifier, toy_children))

        # At each node of `small`, the Classified output must match
        # the corresponding node in `large` when reached via the
        # left subtree.  The first node of `small` is its root (zpath=1);
        # in `large`, the small root appears as zpath=0b10 (root→left).
        # Extract by matching Classified content at corresponding tree
        # positions (pre-order, same index):
        assert small_walk[0][1] == large_walk[1][1]  # small root = large.left
        assert small_walk[1][1] == large_walk[2][1]  # small.left = large.left.left
        assert small_walk[2][1] == large_walk[3][1]  # small.right = large.left.right
