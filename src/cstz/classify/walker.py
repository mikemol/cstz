"""Walker — traversal and z-path encoding.

Invariant: traversal defines order; encoding defines identity.
Neither observes discriminator semantics.

The walker's job is to traverse a tree and compose τ-signatures
along a z-path.  It does NOT interpret τ; it just records which
node was visited at which path.

z-path encoding is self-delimiting: a sentinel high bit marks the
depth, and the lower bits record the path of left(0)/right(1)
choices from the root.  Depth 0 (root) → 0b1 = 1; path [0, 1] at
depth 2 → 0b1_01 = 5.

Monotonicity: descending deeper yields new (zpath, Classified)
pairs at new z-paths.  Previously yielded pairs are never modified.
GF(2) cancellation is confined to single-node τ composition within
classify(); cross-node cancellation is not permitted here.
"""

from __future__ import annotations

from typing import Any, Callable, Iterator, Tuple

from cstz.classify.base import Classified, Classifier


def zpath(bits: int, depth: int) -> int:
    """Self-delimiting z-path encoding.

    The high bit at position `depth` is the sentinel; the lower
    `depth` bits record the path (0 = left, 1 = right).

    Examples:
        zpath(0, 0)   == 0b1        (root)
        zpath(0, 1)   == 0b10       (root → left)
        zpath(1, 1)   == 0b11       (root → right)
        zpath(0b01, 2) == 0b101     (root → left → right)
        zpath(0b11, 2) == 0b111     (root → right → right)
    """
    if depth < 0:
        raise ValueError(f"depth must be non-negative, got {depth}")
    if bits < 0 or (depth > 0 and bits >= (1 << depth)):
        raise ValueError(f"bits {bits} out of range for depth {depth}")
    return (1 << depth) | bits


# A children function maps a node to a tuple of (role_name, child) pairs.
# Roles are informational for debugging; the role INDEX (0 or 1)
# encodes the z-path bit.
ChildrenFn = Callable[[Any], Tuple[Tuple[str, Any], ...]]


def walk(
    root: Any,
    classifier: Classifier,
    children_fn: ChildrenFn,
) -> Iterator[Tuple[int, Classified]]:
    """Depth-first walk yielding (zpath, Classified) per node.

    Traversal is pre-order: the node is classified and yielded
    before its children.  Children are visited left-to-right.

    The classifier's shape_of() output determines arity.  If the
    classifier reports arity=0 (leaf), children_fn must return ()
    for that node; otherwise, children_fn must return `arity` pairs.

    Monotonicity: yielded pairs are never modified.  A caller that
    stops iterating after depth d receives exactly the depth-d
    prefix of the full walk.
    """
    yield from _walk_rec(root, classifier, children_fn, bits=0, depth=0)


def _walk_rec(
    node: Any,
    classifier: Classifier,
    children_fn: ChildrenFn,
    bits: int,
    depth: int,
) -> Iterator[Tuple[int, Classified]]:
    classified = classifier.classify(node)
    yield zpath(bits, depth), classified

    arity = classified.shape.arity
    if arity == 0:
        return

    children = children_fn(node)
    if len(children) != arity:
        raise ValueError(
            f"shape arity {arity} but children_fn returned "
            f"{len(children)} children at depth {depth}"
        )

    for i, (_role, child) in enumerate(children):
        # i ∈ {0, 1} for binary; i ∈ {0} for unary.
        child_bits = (bits << 1) | i
        yield from _walk_rec(
            child, classifier, children_fn, child_bits, depth + 1
        )
