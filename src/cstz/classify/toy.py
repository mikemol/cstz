"""Toy binary-tree classifier — exercises the whole pipeline.

A minimal concrete classifier to validate the API:

    ToyNode is either a leaf (with integer value) or a branch
    (with two children).

Seven discriminators, each a pure local predicate:

    is_leaf, is_branch, value_even, value_odd,
    has_left_leaf, has_right_leaf, symmetric

End-to-end flow:

    reg = make_toy_registry()
    classifier = ToyBinaryClassifier(reg, tuple(d.id for d in reg.all()))
    state = ObservationState(dim=len(reg))
    patch = state.new_patch()
    emit_patch(walk(tree, classifier, toy_children), patch)
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Tuple

from cstz.classify.base import Classifier, ShapeWitness
from cstz.classify.registry import DiscriminatorRegistry


# ---------------------------------------------------------------------------
# Toy node type
# ---------------------------------------------------------------------------


@dataclass
class ToyNode:
    """Binary tree node: leaf or branch."""
    kind: str                               # "leaf" or "branch"
    value: int = 0
    left: Optional["ToyNode"] = None
    right: Optional["ToyNode"] = None


# ---------------------------------------------------------------------------
# Discriminator registry
# ---------------------------------------------------------------------------


def make_toy_registry() -> DiscriminatorRegistry:
    """Build a DiscriminatorRegistry for the toy domain.

    Seven discriminators:
      is_leaf, is_branch: kind test
      value_even, value_odd: leaf value parity
      has_left_leaf, has_right_leaf: immediate-child-kind test
      symmetric: branch with same-kind children
    """
    reg = DiscriminatorRegistry()

    reg.register(
        "is_leaf",
        lambda n: n.kind == "leaf",
        doc="Fires when the node is a leaf.",
    )
    reg.register(
        "is_branch",
        lambda n: n.kind == "branch",
        doc="Fires when the node is a branch.",
    )
    reg.register(
        "value_even",
        lambda n: n.kind == "leaf" and n.value % 2 == 0,
        doc="Leaf with even value.",
    )
    reg.register(
        "value_odd",
        lambda n: n.kind == "leaf" and n.value % 2 == 1,
        doc="Leaf with odd value.",
    )
    reg.register(
        "has_left_leaf",
        lambda n: n.kind == "branch" and n.left is not None
                   and n.left.kind == "leaf",
        doc="Branch whose left child is a leaf.",
    )
    reg.register(
        "has_right_leaf",
        lambda n: n.kind == "branch" and n.right is not None
                   and n.right.kind == "leaf",
        doc="Branch whose right child is a leaf.",
    )
    reg.register(
        "symmetric",
        lambda n: n.kind == "branch" and n.left is not None
                   and n.right is not None
                   and n.left.kind == n.right.kind,
        doc="Branch with same-kind children.",
    )

    return reg


# ---------------------------------------------------------------------------
# Classifier
# ---------------------------------------------------------------------------


class ToyBinaryClassifier(Classifier):
    """Shape-of() for the toy domain: leaves are arity 0, branches arity 2."""

    def shape_of(self, node: Any) -> ShapeWitness:
        if node.kind == "leaf":
            return ShapeWitness(arity=0, roles=())
        return ShapeWitness(arity=2, roles=("left", "right"))


# ---------------------------------------------------------------------------
# Children function — for use with walker.walk()
# ---------------------------------------------------------------------------


def toy_children(node: ToyNode) -> Tuple[Tuple[str, ToyNode], ...]:
    """Return the two children of a branch, or () for a leaf."""
    if node.kind == "leaf":
        return ()
    assert node.left is not None and node.right is not None
    return (("left", node.left), ("right", node.right))
