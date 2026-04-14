"""Python AST classifier — fully coordinate-derived identity.

Identity is computed from intrinsic coordinates only; no pre-order
indices, no traversal artifacts.  Every node's key is determined by
its own fields (constructor tag + parent_key + coordinate triple).

Five variants, all arity 0 or 2 (uniform binary world):

    AstNil                                                    -- gap
    AstScalar(kind, subkind, value, parent_key, ordinal)      -- leaf
    AstField(parent_key, field_ordinal, name_scalar, value)   -- arity 2
    AstListSeg(parent_key, lo, length, left, right)           -- arity 2
    AstNodeWrap(ast_class, kind_bucket,                       -- arity 2
                parent_key, ordinal, fields_root)                (fields, Nil)

Arity:  Nil, Scalar → 0;  Field, ListSeg, NodeWrap → 2
        (NodeWrap's second child is always AstNil — preserves uniform
        binary world without adding new walker mechanics.)

Ordinal convention within a Field:
    0        → name_scalar (the name slot)
    1        → direct (non-list) value
    2 + i    → i-th element of a list-valued field (stable across
               ListSeg rebalancing because parent_key is the Field,
               not any particular ListSeg)

Key scheme — 3-bit constructor tag in low bits, Morton-interleaved
coordinates in high bits:

    key_nil        = 0
    key_scalar     = (morton2(parent_key, ordinal) << 3)      | 0b001
    key_field      = (morton2(parent_key, field_ordinal) <<3) | 0b010
    key_list_seg   = (morton2(parent_key, morton2(lo, len))<<3)| 0b011
    key_node_wrap  = (morton2(parent_key, ordinal) << 3)      | 0b100

Walker / classifier / registry mechanics unchanged from Phases 1-2.
Phase 3 adds only new node variants and new discriminator families.

Identity mode: **positional**, not payload-sensitive.  Two AstScalars
at the same (parent_key, ordinal) share a key regardless of their
`value` field; discriminators see the value via `kind`/`subkind` but
the structural identity is positional.  This matches the "program
shape, not values" regime.

Payload-sensitive identity (classic AST-interning where `42` and `43`
at the same position have different keys) is achievable without
abandoning coordinate-derived identity: represent payload as
structure (e.g. a ScalarValue subtree of bits).  That is a future
extension beyond Phase 3's scope; stopping at positional identity
here keeps the wrapper minimal and matches the Phase 2 precedent
where ByteLeaf keys depend on index, not value.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass
from typing import Any, List, Optional, Tuple, Union

from cstz.classify.base import Classifier, ShapeWitness
from cstz.classify.bytes import morton2
from cstz.classify.registry import DiscriminatorRegistry


# ---------------------------------------------------------------------------
# Constructor tags — part of the structural language, not collision avoidance
# ---------------------------------------------------------------------------

TAG_NIL = 0b000
TAG_SCALAR = 0b001
TAG_FIELD = 0b010
TAG_LIST_SEG = 0b011
TAG_NODE_WRAP = 0b100

# Reserved ordinals within a Field
SLOT_NAME = 0          # the name_scalar
SLOT_DIRECT_VALUE = 1  # non-list field value
SLOT_LIST_OFFSET = 2   # i-th list element lives at SLOT_LIST_OFFSET + i


# ---------------------------------------------------------------------------
# Node variants — a typed structural language, uniform binary
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AstNil:
    """Arity 0.  Gap: missing optional, empty list, or absent payload."""


@dataclass(frozen=True)
class AstScalar:
    """Arity 0.  A primitive, terminal AST atom, or structural label.

    Covers:
      - Python primitives (int, float, str, bool, bytes, None)
      - zero-field AST classes (ast.Load, ast.Store, ast.Add, ...)
      - field-name labels (kind='field_name')

    Attributes:
        kind:       bucket tag — int/float/str/bool/None/bytes/
                    context/op/field_name/unknown
        subkind:    specific type or AST class name
        value:      payload (None for context/op classes)
        parent_key: enclosing Field's key (or 0 for standalone / root)
        ordinal:    0 (name), 1 (direct value), or 2+i (list element i)
    """
    kind: str
    subkind: str
    value: Any
    parent_key: int
    ordinal: int


@dataclass(frozen=True)
class AstField:
    """Arity 2.  Binary decomposition: (name_scalar, value).

    Attributes:
        parent_key:    enclosing AstNodeWrap's key
        field_ordinal: position in parent._fields
        name_scalar:   AstScalar with kind='field_name'
        value:         the field's value subtree
    """
    parent_key: int
    field_ordinal: int
    name_scalar: AstScalar
    value: "AstTree"


@dataclass(frozen=True)
class AstListSeg:
    """Arity 2.  Balanced binary segment of a Python list field.

    Identity uses (parent_key, lo, length) via nested Morton
    composition — distinct subsegments of the same list get distinct
    keys even when they share a starting lo.

    Attributes:
        parent_key:  enclosing AstField's key
        lo:          starting absolute index within the list
        length:      number of items in this segment
        left, right: subtree halves
    """
    parent_key: int
    lo: int
    length: int
    left: "AstTree"
    right: "AstTree"


@dataclass(frozen=True)
class AstNodeWrap:
    """Arity 2.  Wraps a real Python AST node.

    Second child is always AstNil — preserves uniform binary world.
    The fields_root (first child) is either AstNil (zero-field
    shouldn't occur here — those become AstScalar), a single
    AstField, or an AstListSeg tree over AstField leaves.

    Attributes:
        ast_class:   Python AST class name (e.g. "Module", "Call")
        kind_bucket: semantic bucket — "statement"/"expression"/...
        parent_key:  enclosing container's key (0 for root)
        ordinal:     position within parent (0 if root, 1 if direct
                     field value, 2+i for list element i)
        fields_root: binarized field tree
    """
    ast_class: str
    kind_bucket: str
    parent_key: int
    ordinal: int
    fields_root: "AstTree"


AstTree = Union[AstNil, AstScalar, AstField, AstListSeg, AstNodeWrap]


# ---------------------------------------------------------------------------
# Key function — fully coordinate-derived, no traversal indices
# ---------------------------------------------------------------------------


def ast_key(node: AstTree) -> int:
    """Compute a node's intrinsic key.  Pure function of node's own fields."""
    if isinstance(node, AstNil):
        return 0
    if isinstance(node, AstScalar):
        return (morton2(node.parent_key, node.ordinal) << 3) | TAG_SCALAR
    if isinstance(node, AstField):
        return (morton2(node.parent_key, node.field_ordinal) << 3) | TAG_FIELD
    if isinstance(node, AstListSeg):
        q = morton2(node.lo, node.length)
        return (morton2(node.parent_key, q) << 3) | TAG_LIST_SEG
    if isinstance(node, AstNodeWrap):
        return (morton2(node.parent_key, node.ordinal) << 3) | TAG_NODE_WRAP
    raise TypeError(f"unknown AstTree variant: {type(node)!r}")  # pragma: no cover


# ---------------------------------------------------------------------------
# Children function
# ---------------------------------------------------------------------------


def ast_children(node: AstTree) -> Tuple[Tuple[str, AstTree], ...]:
    """Return (role, child) pairs.  Uniform binary for all non-leaves."""
    if isinstance(node, AstField):
        return (("name", node.name_scalar), ("value", node.value))
    if isinstance(node, AstListSeg):
        return (("left", node.left), ("right", node.right))
    if isinstance(node, AstNodeWrap):
        return (("fields_root", node.fields_root), ("trailer", AstNil()))
    return ()


# ---------------------------------------------------------------------------
# Classifier — shape_of is node-local
# ---------------------------------------------------------------------------


class AstClassifier(Classifier):
    """shape_of: Nil/Scalar → 0; Field/ListSeg/NodeWrap → 2."""

    def shape_of(self, node: Any) -> ShapeWitness:
        if isinstance(node, AstField):
            return ShapeWitness(arity=2, roles=("name", "value"))
        if isinstance(node, AstListSeg):
            return ShapeWitness(arity=2, roles=("left", "right"))
        if isinstance(node, AstNodeWrap):
            return ShapeWitness(arity=2, roles=("fields_root", "trailer"))
        return ShapeWitness(arity=0, roles=())


# ---------------------------------------------------------------------------
# AST class categorization (for kind_bucket)
# ---------------------------------------------------------------------------

_CONTEXT_CLASSES = frozenset({
    "Load", "Store", "Del", "AugLoad", "AugStore", "Param",
})

_STATEMENT_CLASSES = frozenset({
    "Module", "Interactive", "Expression",
    "FunctionDef", "AsyncFunctionDef", "ClassDef",
    "Return", "Delete", "Assign", "AugAssign", "AnnAssign",
    "For", "AsyncFor", "While", "If", "With", "AsyncWith",
    "Raise", "Try", "Assert", "Import", "ImportFrom",
    "Global", "Nonlocal", "Expr", "Pass", "Break", "Continue",
    "Match", "MatchCase",
})

_EXPRESSION_CLASSES = frozenset({
    "BoolOp", "BinOp", "UnaryOp", "Lambda", "IfExp", "Dict", "Set",
    "ListComp", "SetComp", "DictComp", "GeneratorExp",
    "Await", "Yield", "YieldFrom", "Compare", "Call",
    "FormattedValue", "JoinedStr", "Constant", "Attribute",
    "Subscript", "Starred", "Name", "List", "Tuple",
    "NamedExpr", "Slice",
})

_COMPREHENSION_CLASSES = frozenset({"comprehension"})

_OPERATOR_CLASSES = frozenset({
    "Add", "Sub", "Mult", "MatMult", "Div", "Mod", "Pow",
    "LShift", "RShift", "BitOr", "BitXor", "BitAnd", "FloorDiv",
    "Invert", "Not", "UAdd", "USub",
    "And", "Or",
    "Eq", "NotEq", "Lt", "LtE", "Gt", "GtE", "Is", "IsNot", "In", "NotIn",
})


def _kind_bucket_for(ast_class: str) -> str:
    if ast_class in _STATEMENT_CLASSES:
        return "statement"
    if ast_class in _EXPRESSION_CLASSES:
        return "expression"
    if ast_class in _CONTEXT_CLASSES:  # pragma: no cover — context classes are zero-field, become Scalars
        return "context"
    if ast_class in _COMPREHENSION_CLASSES:
        return "comprehension"
    if ast_class in _OPERATOR_CLASSES:  # pragma: no cover — operator classes are zero-field, become Scalars
        return "op"
    return "other"  # pragma: no cover


def _primitive_kind_subkind(value: Any) -> Tuple[str, str]:
    if value is None:  # pragma: no cover — None payloads become AstNil
        return ("None", "NoneType")
    if isinstance(value, bool):
        return ("bool", "bool")
    if isinstance(value, int):
        return ("int", "int")
    if isinstance(value, float):
        return ("float", "float")
    if isinstance(value, str):
        return ("str", "str")
    if isinstance(value, bytes):
        return ("bytes", "bytes")
    return ("unknown", type(value).__name__)  # pragma: no cover


# ---------------------------------------------------------------------------
# Tree construction — fully coordinate-driven, no indices
# ---------------------------------------------------------------------------


def parse_to_tree(source: str) -> AstTree:
    """Parse Python source and build the wrapper tree."""
    return module_to_tree(ast.parse(source))


def module_to_tree(root: ast.AST) -> AstTree:
    """Convert an already-parsed ast.AST into an AstTree.

    The root is attached under parent_key=0, ordinal=0.
    """
    return _build_ast_node(root, parent_key=0, ordinal=0)


def _build_ast_node(
    node: ast.AST,
    parent_key: int,
    ordinal: int,
) -> AstTree:
    """Convert an ast.AST node to AstNodeWrap or (for zero-field classes)
    to AstScalar."""
    ast_class = type(node).__name__
    fields = node._fields

    if not fields:
        # Zero-field AST class: Load, Store, Del, Add, Sub, etc. → Scalar
        if ast_class in _CONTEXT_CLASSES:
            kind = "context"
        elif ast_class in _OPERATOR_CLASSES:
            kind = "op"
        else:  # pragma: no cover
            kind = "unknown"
        return AstScalar(
            kind=kind, subkind=ast_class, value=None,
            parent_key=parent_key, ordinal=ordinal,
        )

    # Compute this node's key to pass as parent_key for its fields
    my_key = (morton2(parent_key, ordinal) << 3) | TAG_NODE_WRAP

    # Build each AstField
    field_trees: List[AstField] = []
    for fo, fname in enumerate(fields):
        fval = getattr(node, fname, None)
        field_trees.append(_build_field(fname, my_key, fo, fval))

    # Binarize fields under a ListSeg tree parented by my_key
    fields_root = _binarize_fields(field_trees, parent_key=my_key)

    return AstNodeWrap(
        ast_class=ast_class,
        kind_bucket=_kind_bucket_for(ast_class),
        parent_key=parent_key,
        ordinal=ordinal,
        fields_root=fields_root,
    )


def _build_field(
    fname: str,
    parent_key: int,
    field_ordinal: int,
    value: Any,
) -> AstField:
    """Build an AstField with (name_scalar, value)."""
    # Field's own key, which becomes parent_key for the name and value
    field_key = (morton2(parent_key, field_ordinal) << 3) | TAG_FIELD

    name_scalar = AstScalar(
        kind="field_name", subkind="str", value=fname,
        parent_key=field_key, ordinal=SLOT_NAME,
    )

    if value is None:
        value_tree: AstTree = AstNil()
    elif isinstance(value, list):
        value_tree = (AstNil() if not value
                      else _build_list(value, parent_key=field_key))
    elif isinstance(value, ast.AST):
        value_tree = _build_ast_node(value, parent_key=field_key,
                                      ordinal=SLOT_DIRECT_VALUE)
    else:
        kind, subkind = _primitive_kind_subkind(value)
        value_tree = AstScalar(
            kind=kind, subkind=subkind, value=value,
            parent_key=field_key, ordinal=SLOT_DIRECT_VALUE,
        )

    return AstField(
        parent_key=parent_key,
        field_ordinal=field_ordinal,
        name_scalar=name_scalar,
        value=value_tree,
    )


def _build_list(items: List[Any], parent_key: int) -> AstTree:
    """Balance-binarize a non-empty list of values into an AstListSeg tree.

    Elements' parent_key = the enclosing Field's key (stable across
    ListSeg rebalancing).  Elements' ordinals start at SLOT_LIST_OFFSET.
    """
    return _list_seg(items, parent_key=parent_key, lo=0)


def _list_seg(items: List[Any], parent_key: int, lo: int) -> AstTree:
    n = len(items)
    if n == 1:
        return _build_list_item(items[0], parent_key=parent_key,
                                 ordinal=SLOT_LIST_OFFSET + lo)
    mid = n // 2
    return AstListSeg(
        parent_key=parent_key,
        lo=lo,
        length=n,
        left=_list_seg(items[:mid], parent_key, lo),
        right=_list_seg(items[mid:], parent_key, lo + mid),
    )


def _build_list_item(item: Any, parent_key: int, ordinal: int) -> AstTree:
    if item is None:  # pragma: no cover — Python AST list fields don't contain None
        return AstNil()
    if isinstance(item, ast.AST):
        return _build_ast_node(item, parent_key=parent_key, ordinal=ordinal)
    kind, subkind = _primitive_kind_subkind(item)
    return AstScalar(
        kind=kind, subkind=subkind, value=item,
        parent_key=parent_key, ordinal=ordinal,
    )


def _binarize_fields(
    fields: List[AstField],
    parent_key: int,
) -> AstTree:
    """Binarize a list of AstField leaves under AstListSeg."""
    n = len(fields)
    if n == 0:
        return AstNil()  # pragma: no cover
    if n == 1:
        return fields[0]
    return _fields_seg(fields, parent_key, lo=0)


def _fields_seg(
    fields: List[AstField],
    parent_key: int,
    lo: int,
) -> AstTree:
    n = len(fields)
    if n == 1:
        return fields[0]
    mid = n // 2
    return AstListSeg(
        parent_key=parent_key,
        lo=lo,
        length=n,
        left=_fields_seg(fields[:mid], parent_key, lo),
        right=_fields_seg(fields[mid:], parent_key, lo + mid),
    )


# ---------------------------------------------------------------------------
# Discriminator registries — organized as families
# ---------------------------------------------------------------------------


def make_structural_registry(
    reg: Optional[DiscriminatorRegistry] = None,
) -> DiscriminatorRegistry:
    """Structural family: one discriminator per constructor."""
    if reg is None:
        reg = DiscriminatorRegistry()

    reg.register("is_nil",
                 lambda n: isinstance(n, AstNil),
                 doc="Fires on AstNil.")
    reg.register("is_scalar",
                 lambda n: isinstance(n, AstScalar),
                 doc="Fires on AstScalar.")
    reg.register("is_field",
                 lambda n: isinstance(n, AstField),
                 doc="Fires on AstField.")
    reg.register("is_list_seg",
                 lambda n: isinstance(n, AstListSeg),
                 doc="Fires on AstListSeg.")
    reg.register("is_node_wrap",
                 lambda n: isinstance(n, AstNodeWrap),
                 doc="Fires on AstNodeWrap.")
    return reg


def make_category_registry(
    reg: Optional[DiscriminatorRegistry] = None,
) -> DiscriminatorRegistry:
    """Category family: bucketed by semantic role."""
    if reg is None:
        reg = DiscriminatorRegistry()

    for bucket in ("statement", "expression", "context", "op",
                    "comprehension", "other"):
        reg.register(
            f"bucket_{bucket}",
            (lambda n, b=bucket:
                (isinstance(n, AstNodeWrap) and n.kind_bucket == b)
                or (isinstance(n, AstScalar) and n.kind == b)),
            doc=f"Fires on nodes whose semantic bucket is {bucket!r}.",
        )
    return reg


def make_ast_class_registry(
    reg: Optional[DiscriminatorRegistry] = None,
    classes: Optional[Tuple[str, ...]] = None,
) -> DiscriminatorRegistry:
    """Class family: one `class_<Name>` discriminator per AST class."""
    if reg is None:
        reg = DiscriminatorRegistry()
    if classes is None:
        classes = tuple(sorted(_STATEMENT_CLASSES | _EXPRESSION_CLASSES))
    for cls in classes:
        reg.register(
            f"class_{cls}",
            (lambda n, c=cls:
                isinstance(n, AstNodeWrap) and n.ast_class == c),
            doc=f"AstNodeWrap with ast_class={cls!r}.",
        )
    return reg


def make_field_registry(
    reg: Optional[DiscriminatorRegistry] = None,
    names: Optional[Tuple[str, ...]] = None,
) -> DiscriminatorRegistry:
    """Field family: discriminators keyed by field name."""
    if reg is None:
        reg = DiscriminatorRegistry()
    if names is None:
        names = (
            "body", "args", "targets", "target", "value", "values",
            "test", "orelse", "func", "keywords", "name", "id",
            "op", "ops", "left", "right", "comparators",
            "elts", "keys", "attr", "ctx", "returns",
            "decorator_list", "bases", "iter", "handlers", "finalbody",
            "module", "names", "level", "asname",
            "arg", "annotation", "type_comment",
        )
    for nm in names:
        reg.register(
            f"field_{nm}",
            (lambda n, k=nm:
                isinstance(n, AstField)
                and isinstance(n.name_scalar, AstScalar)
                and n.name_scalar.value == k),
            doc=f"AstField whose name is {nm!r}.",
        )
    return reg


def make_scalar_kind_registry(
    reg: Optional[DiscriminatorRegistry] = None,
) -> DiscriminatorRegistry:
    """Scalar family: one discriminator per scalar kind bucket."""
    if reg is None:
        reg = DiscriminatorRegistry()
    for kind in ("int", "float", "str", "bool", "None", "bytes",
                 "op", "context", "field_name", "unknown"):
        reg.register(
            f"scalar_{kind}",
            (lambda n, k=kind:
                isinstance(n, AstScalar) and n.kind == k),
            doc=f"AstScalar with kind={kind!r}.",
        )
    return reg


def make_list_registry(
    reg: Optional[DiscriminatorRegistry] = None,
) -> DiscriminatorRegistry:
    """List-structure family: shape discriminators on AstListSeg."""
    if reg is None:
        reg = DiscriminatorRegistry()

    reg.register("list_singleton_seg",
                 lambda n: isinstance(n, AstListSeg) and n.length == 1,
                 doc="AstListSeg of length 1.")
    reg.register("list_len_even",
                 lambda n: isinstance(n, AstListSeg) and n.length % 2 == 0,
                 doc="AstListSeg with even length.")
    reg.register("list_len_power_of_two",
                 lambda n: (isinstance(n, AstListSeg) and n.length > 0
                             and (n.length & (n.length - 1)) == 0),
                 doc="AstListSeg with power-of-two length.")
    reg.register("list_starts_at_zero",
                 lambda n: isinstance(n, AstListSeg) and n.lo == 0,
                 doc="AstListSeg covering the start of the parent list.")
    return reg


def make_naming_registry(
    reg: Optional[DiscriminatorRegistry] = None,
) -> DiscriminatorRegistry:
    """Naming-convention family for str-kind scalars."""
    if reg is None:
        reg = DiscriminatorRegistry()

    def _str_and(pred):
        return lambda n: (
            isinstance(n, AstScalar)
            and n.kind == "str"
            and isinstance(n.value, str)
            and pred(n.value)
        )

    reg.register("name_underscore_prefix",
                 _str_and(lambda s: bool(s) and s.startswith("_")
                          and not s.startswith("__")),
                 doc="Starts with exactly one underscore.")
    reg.register("name_dunder",
                 _str_and(lambda s: s.startswith("__") and s.endswith("__")),
                 doc="Dunder name.")
    reg.register("name_all_caps",
                 _str_and(lambda s: s.isupper() and s.isidentifier()),
                 doc="ALL_CAPS identifier.")
    reg.register("name_capitalized",
                 _str_and(lambda s: bool(s) and s[0].isupper()),
                 doc="Starts with uppercase.")
    reg.register("name_snake_case",
                 _str_and(lambda s: s.islower() and "_" in s),
                 doc="Lowercase with underscores.")
    return reg
