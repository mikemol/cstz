"""Byte stream classifier — balanced segment tree + Morton keys.

Represents a byte stream as a balanced binary segment tree:

    ByteNil                           -- gap base case (empty stream)
    ByteLeaf(value, index)            -- byte value at absolute position
    ByteSeg(lo, hi, left, right)      -- concatenation segment [lo, hi)

Arity is purely structural (node-local):
    Nil  → 0
    Leaf → 0
    Seg  → 2 (roles: "left", "right")

No "last byte" checks, no optional-next pointers: termination is
explicit via Nil.  The classifier is pure and local per the
contract; discriminators inspect only a single node's intrinsic
fields.

Keys are computed coordinates via Morton-style bit interleaving.
The low bit is the constructor tag (structural), not metadata:

    key_nil       = 0
    key_leaf(i)   = (i << 1) | 1          -- odd
    key_seg(l,ln) = (morton2(l, ln) << 1) -- even

Leaf keys are odd; Nil and Seg keys are even.  Leaf keys are unique
per byte index and stable across reconstruction: the same byte
stream always produces the same leaf keys regardless of how the
segment tree was built.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Tuple, Union

from cstz.classify.base import Classifier, ShapeWitness
from cstz.classify.registry import DiscriminatorRegistry


# ---------------------------------------------------------------------------
# Node types — balanced segment tree over bytes
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ByteNil:
    """Semantic gap base case: the empty byte stream.

    Arity 0.  No children.  No byte content.  A node-local
    representation of "nothing to observe".
    """


@dataclass(frozen=True)
class ByteLeaf:
    """A single byte at its absolute position in the stream.

    Attributes:
        value: the byte value, 0..255
        index: absolute position in the stream (intrinsic coordinate)
    """
    value: int
    index: int


@dataclass(frozen=True)
class ByteSeg:
    """A concatenation segment of two subtrees covering [lo, hi).

    Attributes:
        lo:    inclusive start index
        hi:    exclusive end index
        left:  left subtree
        right: right subtree

    The segment's identity is `(lo, length)` with length = hi - lo.
    """
    lo: int
    hi: int
    left: "ByteNode"
    right: "ByteNode"


ByteNode = Union[ByteNil, ByteLeaf, ByteSeg]


# ---------------------------------------------------------------------------
# Morton bit-interleaving
# ---------------------------------------------------------------------------


def morton2(a: int, b: int) -> int:
    """2D Morton code: interleave bits of `a` and `b`.

    Bit i of `a` → position 2i
    Bit i of `b` → position 2i+1

    Z-order is defined as bit-interleaving coordinate bits into a
    single integer key.  Pure function; same inputs → same key.
    """
    if a < 0 or b < 0:
        raise ValueError("morton2 requires non-negative inputs")
    result = 0
    shift = 0
    while a or b:
        result |= (a & 1) << shift
        result |= (b & 1) << (shift + 1)
        a >>= 1
        b >>= 1
        shift += 2
    return result


# ---------------------------------------------------------------------------
# Key function — pure coordinate computation
# ---------------------------------------------------------------------------


def byte_key(node: ByteNode) -> int:
    """Compute a ByteNode's zpath/key from its intrinsic coordinates.

    Keys are constructor-tagged (low bit):

        Nil  → 0             (even)
        Leaf → (index<<1)|1  (odd)
        Seg  → (morton2(lo, length)<<1)  (even, length = hi-lo)

    Pure function of the node itself; no traversal context.
    Leaf keys are stable across reconstructions with the same byte
    indices.
    """
    if isinstance(node, ByteNil):
        return 0
    if isinstance(node, ByteLeaf):
        return (node.index << 1) | 1
    if isinstance(node, ByteSeg):
        length = node.hi - node.lo
        return morton2(node.lo, length) << 1
    raise TypeError(f"unknown ByteNode variant: {type(node)!r}")  # pragma: no cover


# ---------------------------------------------------------------------------
# Tree construction — balanced binary from bytes
# ---------------------------------------------------------------------------


def bytes_to_tree(data: bytes) -> ByteNode:
    """Build a balanced binary segment tree over a byte stream.

    Empty input → ByteNil.
    Single byte → ByteLeaf(value, index=0).
    Multiple bytes → ByteSeg with recursive midpoint split.

    Indices are absolute (0..len-1).  Segment split is deterministic:
    left half gets floor(n/2) bytes, right half gets the remainder.
    Reconstruction with the same byte array produces an identical
    tree (leaf keys and segment keys invariant).
    """
    if len(data) == 0:
        return ByteNil()
    return _build(data, lo=0)


def _build(data: bytes, lo: int) -> ByteNode:
    n = len(data)
    if n == 1:
        return ByteLeaf(value=data[0], index=lo)
    mid = n // 2
    return ByteSeg(
        lo=lo,
        hi=lo + n,
        left=_build(data[:mid], lo),
        right=_build(data[mid:], lo + mid),
    )


# ---------------------------------------------------------------------------
# Children function
# ---------------------------------------------------------------------------


def byte_children(node: ByteNode) -> Tuple[Tuple[str, ByteNode], ...]:
    """Return (role, child) pairs for a ByteNode.

    Nil and Leaf return ();  Seg returns (("left", left), ("right", right)).
    """
    if isinstance(node, ByteSeg):
        return (("left", node.left), ("right", node.right))
    return ()


# ---------------------------------------------------------------------------
# Classifier
# ---------------------------------------------------------------------------


class ByteClassifier(Classifier):
    """shape_of for byte trees: Nil=0, Leaf=0, Seg=2.

    Arity depends only on the node's constructor, not on any
    context.  This is the structural locality guarantee: no
    "is this last?" or context-leak needed.
    """

    def shape_of(self, node: Any) -> ShapeWitness:
        if isinstance(node, ByteSeg):
            return ShapeWitness(arity=2, roles=("left", "right"))
        return ShapeWitness(arity=0, roles=())


# ---------------------------------------------------------------------------
# Registries
# ---------------------------------------------------------------------------


def make_ascii_registry() -> DiscriminatorRegistry:
    """Registry of ASCII-category discriminators for byte leaves.

    All discriminators are pure and node-local; they inspect only
    the ByteLeaf's value field.  Non-leaf nodes never fire.
    """
    reg = DiscriminatorRegistry()

    def _leaf_and(pred):
        return lambda n: isinstance(n, ByteLeaf) and pred(n.value)

    reg.register("is_leaf",
                 lambda n: isinstance(n, ByteLeaf),
                 doc="Fires when the node is a ByteLeaf.")
    reg.register("is_zero",
                 _leaf_and(lambda v: v == 0),
                 doc="Leaf with value 0x00.")
    reg.register("is_ascii",
                 _leaf_and(lambda v: v < 128),
                 doc="Leaf with 7-bit ASCII value (< 128).")
    reg.register("is_letter",
                 _leaf_and(lambda v: (0x41 <= v <= 0x5A) or (0x61 <= v <= 0x7A)),
                 doc="ASCII letter A-Z or a-z.")
    reg.register("is_digit",
                 _leaf_and(lambda v: 0x30 <= v <= 0x39),
                 doc="ASCII digit 0-9.")
    reg.register("is_whitespace",
                 _leaf_and(lambda v: v in (0x09, 0x0A, 0x0D, 0x20)),
                 doc="ASCII whitespace: tab, LF, CR, space.")
    reg.register("is_control",
                 _leaf_and(lambda v: v < 0x20 or v == 0x7F),
                 doc="ASCII control character.")
    reg.register("is_printable",
                 _leaf_and(lambda v: 0x20 <= v < 0x7F),
                 doc="ASCII printable (including space).")
    return reg


def make_bitwise_registry(reg: DiscriminatorRegistry = None) -> DiscriminatorRegistry:
    """Registry with bit-level discriminators for byte leaves.

    Registers 8 discriminators (`bit_0` through `bit_7`), one per
    bit position of the byte value.  If `reg` is provided, adds
    to that existing registry; otherwise creates a fresh one.
    This supports the "multiple classifiers share one registry"
    stress test.
    """
    if reg is None:
        reg = DiscriminatorRegistry()
    for i in range(8):
        reg.register(
            f"bit_{i}",
            (lambda n, bit=i:
                isinstance(n, ByteLeaf) and bool(n.value & (1 << bit))),
            doc=f"Bit {i} of leaf value is set.",
        )
    return reg


def make_segment_registry(reg: DiscriminatorRegistry = None) -> DiscriminatorRegistry:
    """Registry with segment-level discriminators.

    Discriminators inspect only (lo, hi) of a ByteSeg; they never
    peek into children.
    """
    if reg is None:
        reg = DiscriminatorRegistry()

    def _seg_and(pred):
        return lambda n: isinstance(n, ByteSeg) and pred(n)

    reg.register("is_seg",
                 lambda n: isinstance(n, ByteSeg),
                 doc="Fires when the node is a ByteSeg.")
    reg.register("is_nil",
                 lambda n: isinstance(n, ByteNil),
                 doc="Fires when the node is a ByteNil.")
    reg.register("seg_singleton",
                 _seg_and(lambda n: (n.hi - n.lo) == 1),
                 doc="Segment of length 1 (unusual; normally a leaf).")
    reg.register("seg_len_even",
                 _seg_and(lambda n: (n.hi - n.lo) % 2 == 0),
                 doc="Segment length is even.")
    reg.register("seg_len_power_of_two",
                 _seg_and(lambda n: (n.hi - n.lo) > 0
                                     and ((n.hi - n.lo) & (n.hi - n.lo - 1)) == 0),
                 doc="Segment length is a power of 2.")
    return reg
