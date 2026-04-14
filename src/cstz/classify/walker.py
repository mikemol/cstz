"""Walker — traversal with pluggable keying.

Separates three concerns:

  1. Traversal  — what nodes are visited, in what order (walk)
  2. Classification — τ of each node (done by the classifier)
  3. Keying     — the zpath/coordinate identity of a node (key_fn)

The walker does not interpret τ and does not decide identity
semantics.  Keying is a projection from intrinsic node coordinates
into the z-address space; callers supply a `key_fn` to control it.

Default keying is traversal-based: `zpath(bits, depth)` where depth
is the path length from root and bits encode left(0)/right(1)
choices.  This is appropriate for trees without intrinsic
coordinates.  Byte streams, ASTs, etc. supply their own key_fn
that derives zpath from node-intrinsic properties (e.g. Morton
interleaving of index/range bits).

Invariants:
  - traversal defines order; keying defines identity
  - neither observes discriminator semantics
  - monotonicity: descending yields new (zpath, Classified) pairs
    at new z-paths; previously yielded pairs are never modified
  - cross-node GF(2) cancellation is not permitted here
"""

from __future__ import annotations

from typing import Any, Callable, Iterator, Optional, Tuple

from cstz.classify.base import Classified, Classifier


def zpath(bits: int, depth: int) -> int:
    """Self-delimiting traversal zpath.

    The high bit at position `depth` is the sentinel; the lower
    `depth` bits record the path (0 = left, 1 = right).

    Examples:
        zpath(0, 0)    == 0b1     (root)
        zpath(0, 1)    == 0b10    (root → left)
        zpath(1, 1)    == 0b11    (root → right)
        zpath(0b01, 2) == 0b101   (root → left → right)
    """
    if depth < 0:
        raise ValueError(f"depth must be non-negative, got {depth}")
    if bits < 0 or (depth > 0 and bits >= (1 << depth)):
        raise ValueError(f"bits {bits} out of range for depth {depth}")
    return (1 << depth) | bits


# ---------------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------------

# A children function maps a node to a tuple of (role_name, child) pairs.
# Roles are informational for debugging; the role INDEX (0 or 1) encodes
# the traversal zpath bit.
ChildrenFn = Callable[[Any], Tuple[Tuple[str, Any], ...]]

# A key function maps a node to its zpath/coordinate.  If None is
# supplied to walk(), the default traversal-based zpath(bits, depth)
# is used.
KeyFn = Callable[[Any], int]


# ---------------------------------------------------------------------------
# walk()
# ---------------------------------------------------------------------------


def walk(
    root: Any,
    classifier: Classifier,
    children_fn: ChildrenFn,
    key_fn: Optional[KeyFn] = None,
) -> Iterator[Tuple[int, Classified]]:
    """Depth-first walk yielding (zpath, Classified) per node.

    Traversal is pre-order: the node is classified and yielded
    before its children.  Children are visited left-to-right.

    If `key_fn` is supplied, each yielded zpath is `key_fn(node)`;
    otherwise the default traversal-based zpath(bits, depth) is used.

    `key_fn` must be pure and local to the node's structural record
    (e.g. its intrinsic coordinates).  It must NOT consult traversal
    state, parent, children, or any external context.

    Monotonicity: yielded pairs are never modified.  A caller that
    stops iterating after k items receives exactly the first k pairs
    of the full walk.
    """
    yield from _walk_rec(root, classifier, children_fn,
                         bits=0, depth=0, key_fn=key_fn)


def _walk_rec(
    node: Any,
    classifier: Classifier,
    children_fn: ChildrenFn,
    bits: int,
    depth: int,
    key_fn: Optional[KeyFn],
) -> Iterator[Tuple[int, Classified]]:
    classified = classifier.classify(node)
    if key_fn is None:
        key = zpath(bits, depth)
    else:
        key = key_fn(node)
    yield key, classified

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
            child, classifier, children_fn, child_bits, depth + 1, key_fn
        )
