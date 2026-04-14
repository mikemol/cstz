"""Tests for cstz.classify.pyast — Python AST classifier.

Phase 3 gate checks:
  G1. No walker/classifier/registry mechanics changed
  G2. Every constructor variant is discriminable (no opaque voids)
  G3. Keys computed purely from intrinsic coordinates (no pre-order indices)
  G4. Uniform binary world: all non-terminals arity 2
  G5. Parent-stored identity: parent_key (computed) not parent_index
  G6. ListSeg subsegments of same list distinguishable by (lo, length)
  G7. Rich decomposition: field names are first-class scalar subtrees
  G8. Discriminator families are small and stable (buckets not 1-per-class)
"""

import ast
import pytest
from cstz.classify.adapter import emit_patch
from cstz.classify.base import Classifier, ShapeWitness
from cstz.classify.bytes import morton2
from cstz.classify.pyast import (
    TAG_BITS,
    TAG_NIL, TAG_SCALAR, TAG_FIELD, TAG_LIST_SEG, TAG_NODE_WRAP,
    TAG_INT_ROOT, TAG_INT_WIDTH, TAG_INT_BIT_SEG, TAG_INT_BIT,
    SLOT_NAME, SLOT_DIRECT_VALUE, SLOT_LIST_OFFSET,
    AstNil, AstScalar, AstField, AstListSeg, AstNodeWrap,
    IntRoot, IntWidth, IntBitSeg, IntBit,
    AstClassifier,
    ast_key, ast_children,
    parse_to_tree, module_to_tree,
    make_structural_registry, make_category_registry,
    make_ast_class_registry, make_field_registry,
    make_scalar_kind_registry, make_list_registry,
    make_naming_registry, make_int_registry,
)
from cstz.classify.registry import DiscriminatorRegistry
from cstz.classify.walker import walk
from cstz.framework import ORDERED_TAU
from cstz.observe import ObservationState, Patch


# ---------------------------------------------------------------------------
# Gate G3: no traversal indices — keys from intrinsic coordinates
# ---------------------------------------------------------------------------


class TestG3CoordinateIdentity:
    """Every node's key must be a pure function of its own fields.  No
    dataclass should carry a `pre-order index` field (only coordinates
    like parent_key, ordinal, lo, length)."""

    def test_nil_key_is_zero(self):
        assert ast_key(AstNil()) == 0

    def test_scalar_key_from_parent_ordinal(self):
        s = AstScalar(kind="int", subkind="int", value=42,
                       parent_key=0, ordinal=1)
        assert ast_key(s) == (morton2(0, 1) << TAG_BITS) | TAG_SCALAR

    def test_field_key_from_parent_and_ordinal(self):
        ns = AstScalar(kind="field_name", subkind="str", value="x",
                        parent_key=0, ordinal=SLOT_NAME)
        f = AstField(parent_key=42, field_ordinal=3,
                      name_scalar=ns, value=AstNil())
        assert ast_key(f) == (morton2(42, 3) << TAG_BITS) | TAG_FIELD

    def test_listseg_key_from_nested_morton(self):
        s = AstListSeg(parent_key=100, lo=4, length=8,
                        left=AstNil(), right=AstNil())
        q = morton2(4, 8)
        assert ast_key(s) == (morton2(100, q) << TAG_BITS) | TAG_LIST_SEG

    def test_nodewrap_key_from_parent_and_ordinal(self):
        w = AstNodeWrap(ast_class="Module", kind_bucket="statement",
                         parent_key=0, ordinal=0, fields_root=AstNil())
        assert ast_key(w) == (morton2(0, 0) << TAG_BITS) | TAG_NODE_WRAP


# ---------------------------------------------------------------------------
# Gate G2: every constructor is discriminable (tag disjointness)
# ---------------------------------------------------------------------------


class TestG2TagDisjointness:
    def test_distinct_tags(self):
        all_tags = {TAG_NIL, TAG_SCALAR, TAG_FIELD, TAG_LIST_SEG,
                     TAG_NODE_WRAP, TAG_INT_ROOT, TAG_INT_WIDTH,
                     TAG_INT_BIT_SEG, TAG_INT_BIT}
        assert len(all_tags) == 9

    def test_tags_fit_in_tag_bits(self):
        limit = 1 << TAG_BITS
        for tag in (TAG_NIL, TAG_SCALAR, TAG_FIELD, TAG_LIST_SEG,
                     TAG_NODE_WRAP, TAG_INT_ROOT, TAG_INT_WIDTH,
                     TAG_INT_BIT_SEG, TAG_INT_BIT):
            assert 0 <= tag < limit

    def test_keys_separable_by_tag(self):
        """Different constructors at the same coordinate give distinct keys."""
        pk, o = 7, 3
        s = AstScalar(kind="int", subkind="int", value=0,
                       parent_key=pk, ordinal=o)
        w = AstNodeWrap(ast_class="X", kind_bucket="other",
                         parent_key=pk, ordinal=o, fields_root=AstNil())
        assert ast_key(s) != ast_key(w)
        # Low TAG_BITS bits encode the constructor tag
        mask = (1 << TAG_BITS) - 1
        assert ast_key(s) & mask == TAG_SCALAR
        assert ast_key(w) & mask == TAG_NODE_WRAP


# ---------------------------------------------------------------------------
# Gate G4: uniform binary world (arity 0 or 2)
# ---------------------------------------------------------------------------


class TestG4UniformBinaryShape:
    def _classifier(self):
        return AstClassifier(DiscriminatorRegistry(), ())

    def test_nil_arity_0(self):
        s = self._classifier().shape_of(AstNil())
        assert s.arity == 0

    def test_scalar_arity_0(self):
        s = self._classifier().shape_of(
            AstScalar(kind="int", subkind="int", value=1,
                       parent_key=0, ordinal=0))
        assert s.arity == 0

    def test_field_arity_2(self):
        ns = AstScalar(kind="field_name", subkind="str", value="x",
                        parent_key=0, ordinal=0)
        f = AstField(parent_key=0, field_ordinal=0,
                      name_scalar=ns, value=AstNil())
        s = self._classifier().shape_of(f)
        assert s.arity == 2
        assert s.roles == ("name", "value")

    def test_list_seg_arity_2(self):
        ls = AstListSeg(parent_key=0, lo=0, length=2,
                         left=AstNil(), right=AstNil())
        s = self._classifier().shape_of(ls)
        assert s.arity == 2
        assert s.roles == ("left", "right")

    def test_node_wrap_arity_2_trailer_nil(self):
        w = AstNodeWrap(ast_class="X", kind_bucket="other",
                         parent_key=0, ordinal=0, fields_root=AstNil())
        s = self._classifier().shape_of(w)
        assert s.arity == 2
        assert s.roles == ("fields_root", "trailer")
        # children_fn must emit two children; second is always AstNil
        kids = ast_children(w)
        assert len(kids) == 2
        assert isinstance(kids[1][1], AstNil)


# ---------------------------------------------------------------------------
# Gate G6: ListSeg subsegments disambiguated by (lo, length)
# ---------------------------------------------------------------------------


class TestG6ListSegSubsegmentUniqueness:
    def test_subsegs_share_parent_but_differ_by_len(self):
        """Outer seg (lo=0, length=4) and left inner (lo=0, length=2)
        must have different keys despite same parent_key and lo."""
        outer = AstListSeg(parent_key=7, lo=0, length=4,
                            left=AstNil(), right=AstNil())
        left_inner = AstListSeg(parent_key=7, lo=0, length=2,
                                 left=AstNil(), right=AstNil())
        assert ast_key(outer) != ast_key(left_inner)

    def test_subsegs_at_different_lo(self):
        left = AstListSeg(parent_key=7, lo=0, length=2,
                           left=AstNil(), right=AstNil())
        right = AstListSeg(parent_key=7, lo=2, length=2,
                            left=AstNil(), right=AstNil())
        assert ast_key(left) != ast_key(right)


# ---------------------------------------------------------------------------
# Tree construction
# ---------------------------------------------------------------------------


class TestParseToTree:
    def test_empty_module(self):
        tree = parse_to_tree("")
        assert isinstance(tree, AstNodeWrap)
        assert tree.ast_class == "Module"
        assert tree.kind_bucket == "statement"
        assert tree.parent_key == 0
        assert tree.ordinal == 0

    def test_simple_assignment(self):
        tree = parse_to_tree("x = 1")
        # Module → body list with one Assign
        assert isinstance(tree, AstNodeWrap)
        assert tree.ast_class == "Module"

    def test_function_def(self):
        tree = parse_to_tree("def f(x): return x")
        assert isinstance(tree, AstNodeWrap)
        # Verify the tree contains a FunctionDef somewhere
        found = _find_nodewrap(tree, "FunctionDef")
        assert found is not None

    def test_deterministic(self):
        t1 = parse_to_tree("x = 1\ny = 2")
        t2 = parse_to_tree("x = 1\ny = 2")
        assert t1 == t2


def _find_nodewrap(tree, ast_class):
    """Walk the tree looking for an AstNodeWrap with given ast_class."""
    if isinstance(tree, AstNodeWrap):
        if tree.ast_class == ast_class:
            return tree
        result = _find_nodewrap(tree.fields_root, ast_class)
        if result is not None:
            return result
    if isinstance(tree, AstField):
        return (_find_nodewrap(tree.name_scalar, ast_class)
                or _find_nodewrap(tree.value, ast_class))
    if isinstance(tree, AstListSeg):
        return (_find_nodewrap(tree.left, ast_class)
                or _find_nodewrap(tree.right, ast_class))
    return None


# ---------------------------------------------------------------------------
# Gate G7: field names are first-class scalar subtrees
# ---------------------------------------------------------------------------


class TestG7FieldNameDecomposition:
    def test_field_name_is_scalar_subtree(self):
        tree = parse_to_tree("x = 1")
        # Find an AstField
        field = _find_field(tree, "body")
        assert field is not None
        # name_scalar is a first-class AstScalar with kind='field_name'
        assert isinstance(field.name_scalar, AstScalar)
        assert field.name_scalar.kind == "field_name"
        assert field.name_scalar.value == "body"

    def test_field_name_has_its_own_key(self):
        tree = parse_to_tree("x = 1")
        field = _find_field(tree, "body")
        assert ast_key(field.name_scalar) != ast_key(field)


def _find_field(tree, field_name):
    """Find the first AstField with given name."""
    if isinstance(tree, AstField):
        if isinstance(tree.name_scalar, AstScalar) and tree.name_scalar.value == field_name:
            return tree
        return (_find_field(tree.name_scalar, field_name)
                or _find_field(tree.value, field_name))
    if isinstance(tree, AstListSeg):
        return (_find_field(tree.left, field_name)
                or _find_field(tree.right, field_name))
    if isinstance(tree, AstNodeWrap):
        return _find_field(tree.fields_root, field_name)
    return None


# ---------------------------------------------------------------------------
# Discriminator families (Gate G8: small, stable, bucketed)
# ---------------------------------------------------------------------------


class TestStructuralFamily:
    def test_size(self):
        reg = make_structural_registry()
        assert len(reg) == 5

    def test_coverage(self):
        """Every constructor has a matching discriminator."""
        reg = make_structural_registry()
        names = {d.name for d in reg.all()}
        assert names == {
            "is_nil", "is_scalar", "is_field", "is_list_seg", "is_node_wrap",
        }


class TestCategoryFamily:
    def test_size(self):
        reg = make_category_registry()
        assert len(reg) == 6  # statement/expression/context/op/comprehension/other

    def test_statement_bucket(self):
        reg = make_category_registry()
        d = reg.get_by_name("bucket_statement")
        # A Module is a statement
        mod = AstNodeWrap(ast_class="Module", kind_bucket="statement",
                           parent_key=0, ordinal=0, fields_root=AstNil())
        assert d.fires(mod) is True
        # A Call is an expression, not a statement
        call = AstNodeWrap(ast_class="Call", kind_bucket="expression",
                            parent_key=0, ordinal=0, fields_root=AstNil())
        assert d.fires(call) is False

    def test_context_fires_on_scalar(self):
        reg = make_category_registry()
        d = reg.get_by_name("bucket_context")
        load_scalar = AstScalar(kind="context", subkind="Load", value=None,
                                 parent_key=0, ordinal=0)
        assert d.fires(load_scalar) is True


class TestAstClassFamily:
    def test_default_classes(self):
        reg = make_ast_class_registry()
        assert reg.get_by_name("class_Module") is not None
        assert reg.get_by_name("class_Call") is not None
        assert reg.get_by_name("class_FunctionDef") is not None

    def test_custom_class_list(self):
        reg = make_ast_class_registry(classes=("Call",))
        assert len(reg) == 1

    def test_fires_on_matching_wrap(self):
        reg = make_ast_class_registry()
        d = reg.get_by_name("class_Module")
        mod = AstNodeWrap(ast_class="Module", kind_bucket="statement",
                           parent_key=0, ordinal=0, fields_root=AstNil())
        call = AstNodeWrap(ast_class="Call", kind_bucket="expression",
                            parent_key=0, ordinal=0, fields_root=AstNil())
        assert d.fires(mod) is True
        assert d.fires(call) is False


class TestFieldFamily:
    def test_detects_body_field(self):
        reg = make_field_registry()
        d = reg.get_by_name("field_body")

        ns = AstScalar(kind="field_name", subkind="str", value="body",
                        parent_key=0, ordinal=SLOT_NAME)
        f = AstField(parent_key=0, field_ordinal=0,
                      name_scalar=ns, value=AstNil())
        assert d.fires(f) is True

    def test_does_not_fire_on_other_field(self):
        reg = make_field_registry()
        d = reg.get_by_name("field_body")
        ns = AstScalar(kind="field_name", subkind="str", value="args",
                        parent_key=0, ordinal=SLOT_NAME)
        f = AstField(parent_key=0, field_ordinal=0,
                      name_scalar=ns, value=AstNil())
        assert d.fires(f) is False


class TestScalarKindFamily:
    def test_int_discriminator(self):
        reg = make_scalar_kind_registry()
        d = reg.get_by_name("scalar_int")
        s = AstScalar(kind="int", subkind="int", value=42,
                       parent_key=0, ordinal=0)
        assert d.fires(s) is True
        s2 = AstScalar(kind="str", subkind="str", value="x",
                        parent_key=0, ordinal=0)
        assert d.fires(s2) is False


class TestListFamily:
    def test_singleton(self):
        reg = make_list_registry()
        d = reg.get_by_name("list_singleton_seg")
        seg = AstListSeg(parent_key=0, lo=0, length=1,
                          left=AstNil(), right=AstNil())
        assert d.fires(seg) is True

    def test_power_of_two(self):
        reg = make_list_registry()
        d = reg.get_by_name("list_len_power_of_two")
        for n in (1, 2, 4, 8):
            seg = AstListSeg(parent_key=0, lo=0, length=n,
                              left=AstNil(), right=AstNil())
            assert d.fires(seg) is True
        for n in (3, 5, 7):
            seg = AstListSeg(parent_key=0, lo=0, length=n,
                              left=AstNil(), right=AstNil())
            assert d.fires(seg) is False


class TestNamingFamily:
    def test_dunder(self):
        reg = make_naming_registry()
        d = reg.get_by_name("name_dunder")
        s = AstScalar(kind="str", subkind="str", value="__init__",
                       parent_key=0, ordinal=0)
        assert d.fires(s) is True
        s2 = AstScalar(kind="str", subkind="str", value="foo",
                        parent_key=0, ordinal=0)
        assert d.fires(s2) is False

    def test_underscore_prefix(self):
        reg = make_naming_registry()
        d = reg.get_by_name("name_underscore_prefix")
        s = AstScalar(kind="str", subkind="str", value="_private",
                       parent_key=0, ordinal=0)
        assert d.fires(s) is True
        s2 = AstScalar(kind="str", subkind="str", value="__dunder__",
                        parent_key=0, ordinal=0)
        assert d.fires(s2) is False


# ---------------------------------------------------------------------------
# Gate G1: end-to-end with unchanged walker/classifier/registry machinery
# ---------------------------------------------------------------------------


class TestG1NoMachineryChanges:
    """Phase 3 works with the existing walker, Classifier base, registry,
    and emit_patch, passing only new node types and new discriminators."""

    def test_end_to_end_simple(self):
        reg = make_structural_registry()
        make_category_registry(reg)
        classifier = AstClassifier(reg, tuple(d.id for d in reg.all()))

        tree = parse_to_tree("x = 1")
        patch = Patch()
        emit_patch(
            walk(tree, classifier, ast_children, key_fn=ast_key),
            patch,
        )
        # At least some τ fires
        assert len(patch.observations) > 0
        for obs in patch.observations:
            assert obs.result == ORDERED_TAU

    def test_end_to_end_function_def(self):
        reg = make_structural_registry()
        make_category_registry(reg)
        make_ast_class_registry(reg, classes=("FunctionDef", "Name", "Return"))
        classifier = AstClassifier(reg, tuple(d.id for d in reg.all()))

        tree = parse_to_tree("def f(x): return x")
        state = ObservationState(dim=len(reg))
        patch = state.new_patch()
        emit_patch(
            walk(tree, classifier, ast_children, key_fn=ast_key),
            patch,
        )

        # class_FunctionDef fires at least once
        fd_id = reg.get_by_name("class_FunctionDef").id
        fired_disc = {o.discriminator for o in patch.observations}
        assert fd_id in fired_disc


# ---------------------------------------------------------------------------
# Cross-family composition: the Phase 3 expressive-power test
# ---------------------------------------------------------------------------


class TestCoverageGaps:
    """Targeted tests for branches/paths not exercised by earlier tests."""

    def test_ast_children_on_leaf_returns_empty(self):
        """ast_children on Nil/Scalar returns ()."""
        assert ast_children(AstNil()) == ()
        s = AstScalar(kind="int", subkind="int", value=0,
                       parent_key=0, ordinal=0)
        assert ast_children(s) == ()

    def test_primitive_scalar_kinds(self):
        """Parse sources exercising primitive scalar kinds.

        Note: the Python literal `None` becomes `ast.Constant(value=None)`;
        internally we treat the None payload as "absent" (AstNil) rather
        than a scalar, so kind='None' is not observed through source parse.
        Bool/float/str/bytes are observed as AstScalar.
        Int payloads are decomposed into IntRoot (Phase 4a), not AstScalar;
        see TestG9PayloadSensitiveInt for integer coverage.
        """
        tree = parse_to_tree("True; 1.5; 'x'; b'y'")
        kinds = _collect_scalar_kinds(tree)
        for k in ("float", "str", "bool", "bytes"):
            assert k in kinds, f"missing scalar kind {k!r}"

    def test_global_names_are_string_list_items(self):
        """ast.Global.names is a list of strings — exercises primitive
        list-item path."""
        tree = parse_to_tree("def f():\n    global x, y\n    pass")
        kinds = _collect_scalar_kinds(tree)
        # The global name strings are str-kind scalars
        assert "str" in kinds

    def test_operator_bucket(self):
        """Binary operator firings produce op-kind scalars."""
        tree = parse_to_tree("a + b")
        kinds = _collect_scalar_kinds(tree)
        assert "op" in kinds

    def test_comprehension_bucket(self):
        """List comprehensions include ast.comprehension nodes."""
        tree = parse_to_tree("[x for x in y]")
        buckets = _collect_buckets(tree)
        assert "comprehension" in buckets

    def test_context_bucket(self):
        """Name references include Load/Store context."""
        tree = parse_to_tree("x = y")
        kinds = _collect_scalar_kinds(tree)
        assert "context" in kinds

    def test_registries_with_existing_arg(self):
        """Passing an existing registry to each family factory extends it."""
        base = DiscriminatorRegistry()
        before = len(base)
        make_structural_registry(base)
        make_category_registry(base)
        make_ast_class_registry(base, classes=("Call",))
        make_field_registry(base, names=("body",))
        make_scalar_kind_registry(base)
        make_list_registry(base)
        make_naming_registry(base)
        # Each registered at least one discriminator
        assert len(base) > before + 10

    def test_structural_discriminators_on_wrong_types(self):
        """is_* discriminators must return False on wrong types."""
        reg = make_structural_registry()
        non_nil = AstScalar(kind="int", subkind="int", value=0,
                             parent_key=0, ordinal=0)
        assert reg.get_by_name("is_nil").fires(non_nil) is False
        assert reg.get_by_name("is_scalar").fires(AstNil()) is False
        assert reg.get_by_name("is_field").fires(AstNil()) is False
        assert reg.get_by_name("is_list_seg").fires(AstNil()) is False
        assert reg.get_by_name("is_node_wrap").fires(AstNil()) is False

    def test_category_false_on_wrong_variant(self):
        """bucket_* false path when variant doesn't match."""
        reg = make_category_registry()
        s = AstScalar(kind="int", subkind="int", value=0,
                       parent_key=0, ordinal=0)
        # This scalar has kind "int", not "statement"/"expression"/etc.
        # So bucket_statement should return False
        assert reg.get_by_name("bucket_statement").fires(s) is False
        assert reg.get_by_name("bucket_statement").fires(AstNil()) is False

    def test_field_false_on_non_field(self):
        reg = make_field_registry(names=("body",))
        assert reg.get_by_name("field_body").fires(AstNil()) is False

    def test_scalar_kind_false_on_non_scalar(self):
        reg = make_scalar_kind_registry()
        assert reg.get_by_name("scalar_int").fires(AstNil()) is False

    def test_list_discriminators_on_non_listseg(self):
        reg = make_list_registry()
        for name in ("list_singleton_seg", "list_len_even",
                      "list_len_power_of_two", "list_starts_at_zero"):
            assert reg.get_by_name(name).fires(AstNil()) is False

    def test_naming_discriminators_on_non_scalar(self):
        reg = make_naming_registry()
        for name in ("name_underscore_prefix", "name_dunder",
                      "name_all_caps", "name_capitalized", "name_snake_case"):
            assert reg.get_by_name(name).fires(AstNil()) is False


def _collect_scalar_kinds(tree):
    """Collect all AstScalar.kind values in the tree."""
    kinds = set()
    _walk_collect(tree, kinds, _scalar_kind_of)
    return kinds


def _collect_buckets(tree):
    """Collect all kind_bucket values from AstNodeWrap nodes."""
    buckets = set()
    _walk_collect(tree, buckets, _nodewrap_bucket_of)
    return buckets


def _scalar_kind_of(node):
    return node.kind if isinstance(node, AstScalar) else None


def _nodewrap_bucket_of(node):
    return node.kind_bucket if isinstance(node, AstNodeWrap) else None


def _walk_collect(node, out, extractor):
    v = extractor(node)
    if v is not None:
        out.add(v)
    if isinstance(node, AstField):
        _walk_collect(node.name_scalar, out, extractor)
        _walk_collect(node.value, out, extractor)
    elif isinstance(node, AstListSeg):
        _walk_collect(node.left, out, extractor)
        _walk_collect(node.right, out, extractor)
    elif isinstance(node, AstNodeWrap):
        _walk_collect(node.fields_root, out, extractor)


class TestExpressivePower:
    """Real Python snippets produce sensible τ patterns."""

    def test_class_definition(self):
        reg = make_structural_registry()
        make_category_registry(reg)
        make_ast_class_registry(reg, classes=("ClassDef",))
        classifier = AstClassifier(reg, tuple(d.id for d in reg.all()))

        tree = parse_to_tree("class Foo: pass")
        state = ObservationState(dim=len(reg))
        patch = state.new_patch()
        emit_patch(
            walk(tree, classifier, ast_children, key_fn=ast_key),
            patch,
        )

        fired = {o.discriminator for o in patch.observations}
        assert reg.get_by_name("class_ClassDef").id in fired
        assert reg.get_by_name("bucket_statement").id in fired

    def test_dunder_method_naming(self):
        reg = make_structural_registry()
        make_naming_registry(reg)
        make_scalar_kind_registry(reg)
        classifier = AstClassifier(reg, tuple(d.id for d in reg.all()))

        tree = parse_to_tree(
            "class C:\n    def __init__(self):\n        pass"
        )
        state = ObservationState(dim=len(reg))
        patch = state.new_patch()
        emit_patch(
            walk(tree, classifier, ast_children, key_fn=ast_key),
            patch,
        )

        fired = {o.discriminator for o in patch.observations}
        # __init__ fires name_dunder
        assert reg.get_by_name("name_dunder").id in fired


# ---------------------------------------------------------------------------
# Gate G9 (Phase 4a): payload-sensitive identity for integers
# ---------------------------------------------------------------------------


def _collect_int_nodes(tree):
    """Gather all Int* nodes by walking the structural tree."""
    out = []
    _walk_int(tree, out)
    return out


def _walk_int(node, out):
    if isinstance(node, (IntRoot, IntWidth, IntBitSeg, IntBit)):
        out.append(node)
    if isinstance(node, AstField):
        _walk_int(node.name_scalar, out)
        _walk_int(node.value, out)
    elif isinstance(node, AstListSeg):
        _walk_int(node.left, out)
        _walk_int(node.right, out)
    elif isinstance(node, AstNodeWrap):
        _walk_int(node.fields_root, out)
    elif isinstance(node, IntRoot):
        _walk_int(node.width_marker, out)
        _walk_int(node.bits_root, out)
    elif isinstance(node, IntBitSeg):
        _walk_int(node.left, out)
        _walk_int(node.right, out)


def _find_int_root(tree):
    """First IntRoot found in tree, or None."""
    nodes = _collect_int_nodes(tree)
    for n in nodes:
        if isinstance(n, IntRoot):
            return n
    return None


class TestG9PayloadSensitiveInt:
    """Phase 4a gates: integer payload is represented as structure,
    not as an opaque scalar value.  Identity of each component is
    coordinate-derived; walker/classifier/registry mechanics unchanged."""

    def test_int_key_derivation(self):
        r = IntRoot(parent_key=7, ordinal=1, is_negative=False,
                     width_marker=IntWidth(parent_key=0, width=3),
                     bits_root=AstNil())
        inner = morton2(1, 0)
        assert ast_key(r) == (morton2(7, inner) << TAG_BITS) | TAG_INT_ROOT

    def test_int_width_key_encodes_width(self):
        a = IntWidth(parent_key=0, width=3)
        b = IntWidth(parent_key=0, width=8)
        assert ast_key(a) != ast_key(b)
        assert ast_key(a) & ((1 << TAG_BITS) - 1) == TAG_INT_WIDTH

    def test_int_bit_key_encodes_value(self):
        b0 = IntBit(parent_key=0, position=2, bit=0)
        b1 = IntBit(parent_key=0, position=2, bit=1)
        assert ast_key(b0) != ast_key(b1)
        assert ast_key(b0) & ((1 << TAG_BITS) - 1) == TAG_INT_BIT

    def test_int_bit_seg_subsegs_distinct(self):
        outer = IntBitSeg(parent_key=5, lo=0, length=4,
                           left=AstNil(), right=AstNil())
        inner = IntBitSeg(parent_key=5, lo=0, length=2,
                           left=AstNil(), right=AstNil())
        assert ast_key(outer) != ast_key(inner)

    def test_signs_give_different_int_roots(self):
        pos = _find_int_root(parse_to_tree("x = 1"))
        neg = _find_int_root(parse_to_tree("x = -1"))
        assert pos is not None and neg is not None
        # Unary-minus wraps as ast.UnaryOp, so the literal inside is still
        # positive 1.  Construct a negative IntRoot directly to verify
        # sign is baked into the key.
        pos_direct = IntRoot(parent_key=7, ordinal=1, is_negative=False,
                              width_marker=IntWidth(parent_key=0, width=1),
                              bits_root=AstNil())
        neg_direct = IntRoot(parent_key=7, ordinal=1, is_negative=True,
                              width_marker=IntWidth(parent_key=0, width=1),
                              bits_root=AstNil())
        assert ast_key(pos_direct) != ast_key(neg_direct)

    def test_zero_has_width_zero_and_nil_bits(self):
        r = _build_int_root_zero()
        assert r.width_marker.width == 0
        assert isinstance(r.bits_root, AstNil)

    def test_width_one_has_single_bit(self):
        tree = parse_to_tree("x = 1")
        r = _find_int_root(tree)
        assert r is not None
        assert r.width_marker.width == 1
        assert isinstance(r.bits_root, IntBit)
        assert r.bits_root.bit == 1
        assert r.bits_root.position == 0

    def test_width_ge_two_builds_balanced_seg(self):
        tree = parse_to_tree("x = 5")  # 0b101, width=3
        r = _find_int_root(tree)
        assert r is not None
        assert r.width_marker.width == 3
        assert isinstance(r.bits_root, IntBitSeg)
        # Gather all IntBit leaves to verify the bit pattern
        bits = [n for n in _collect_int_nodes(tree) if isinstance(n, IntBit)]
        at = {b.position: b.bit for b in bits}
        assert at == {0: 1, 1: 0, 2: 1}

    def test_different_values_differ_at_bits(self):
        """x=1 and x=2 produce distinct keys at some IntBit leaf."""
        t1 = parse_to_tree("x = 1")
        t2 = parse_to_tree("x = 2")
        keys1 = {ast_key(n) for n in _collect_int_nodes(t1)
                 if isinstance(n, IntBit)}
        keys2 = {ast_key(n) for n in _collect_int_nodes(t2)
                 if isinstance(n, IntBit)}
        assert keys1 != keys2

    def test_same_value_same_tree(self):
        assert parse_to_tree("x = 42") == parse_to_tree("x = 42")

    def test_uniform_binary_int_shapes(self):
        c = AstClassifier(DiscriminatorRegistry(), ())
        # Arity 2 for IntRoot and IntBitSeg
        r = IntRoot(parent_key=0, ordinal=0, is_negative=False,
                     width_marker=IntWidth(parent_key=0, width=0),
                     bits_root=AstNil())
        assert c.shape_of(r).arity == 2
        assert c.shape_of(r).roles == ("width", "bits")
        seg = IntBitSeg(parent_key=0, lo=0, length=2,
                         left=AstNil(), right=AstNil())
        assert c.shape_of(seg).arity == 2
        assert c.shape_of(seg).roles == ("left", "right")
        # Arity 0 for markers and leaf bits
        assert c.shape_of(IntWidth(parent_key=0, width=0)).arity == 0
        assert c.shape_of(IntBit(parent_key=0, position=0, bit=1)).arity == 0

    def test_int_children(self):
        w = IntWidth(parent_key=0, width=3)
        bits = IntBit(parent_key=0, position=0, bit=1)
        r = IntRoot(parent_key=0, ordinal=1, is_negative=False,
                     width_marker=w, bits_root=bits)
        kids = ast_children(r)
        assert kids == (("width", w), ("bits", bits))
        seg = IntBitSeg(parent_key=0, lo=0, length=2,
                         left=AstNil(), right=bits)
        assert ast_children(seg) == (("left", AstNil()), ("right", bits))
        assert ast_children(IntWidth(parent_key=0, width=0)) == ()
        assert ast_children(IntBit(parent_key=0, position=0, bit=0)) == ()

    def test_int_registry_structural_coverage(self):
        reg = make_int_registry()
        for name in ("is_int_root", "is_int_width", "is_int_bit_seg",
                      "is_int_bit"):
            assert reg.get_by_name(name) is not None

    def test_int_registry_fires_and_silents(self):
        reg = make_int_registry()
        r = IntRoot(parent_key=0, ordinal=0, is_negative=True,
                     width_marker=IntWidth(parent_key=0, width=3),
                     bits_root=AstNil())
        w = IntWidth(parent_key=0, width=0)
        b0 = IntBit(parent_key=0, position=0, bit=0)
        b1 = IntBit(parent_key=0, position=5, bit=1)
        seg = IntBitSeg(parent_key=0, lo=0, length=2,
                         left=AstNil(), right=AstNil())

        assert reg.get_by_name("is_int_root").fires(r) is True
        assert reg.get_by_name("is_int_root").fires(AstNil()) is False
        assert reg.get_by_name("is_int_width").fires(w) is True
        assert reg.get_by_name("is_int_width").fires(r) is False
        assert reg.get_by_name("is_int_bit_seg").fires(seg) is True
        assert reg.get_by_name("is_int_bit_seg").fires(AstNil()) is False
        assert reg.get_by_name("is_int_bit").fires(b1) is True
        assert reg.get_by_name("is_int_bit").fires(AstNil()) is False

        assert reg.get_by_name("int_is_negative").fires(r) is True
        assert reg.get_by_name("int_is_negative").fires(AstNil()) is False
        # width=3 > 0 so not zero
        assert reg.get_by_name("int_is_zero").fires(r) is False
        assert reg.get_by_name("int_is_zero").fires(AstNil()) is False
        zero = IntRoot(parent_key=0, ordinal=0, is_negative=False,
                        width_marker=IntWidth(parent_key=0, width=0),
                        bits_root=AstNil())
        assert reg.get_by_name("int_is_zero").fires(zero) is True

        assert reg.get_by_name("int_bit_zero").fires(b0) is True
        assert reg.get_by_name("int_bit_zero").fires(b1) is False
        assert reg.get_by_name("int_bit_zero").fires(AstNil()) is False
        assert reg.get_by_name("int_bit_one").fires(b1) is True
        assert reg.get_by_name("int_bit_one").fires(b0) is False
        assert reg.get_by_name("int_bit_one").fires(AstNil()) is False
        assert reg.get_by_name("int_bit_lsb").fires(b0) is True
        assert reg.get_by_name("int_bit_lsb").fires(b1) is False
        assert reg.get_by_name("int_bit_lsb").fires(AstNil()) is False

        assert reg.get_by_name("int_width_zero").fires(w) is True
        assert reg.get_by_name("int_width_zero").fires(AstNil()) is False
        byte_w = IntWidth(parent_key=0, width=5)
        big_w = IntWidth(parent_key=0, width=64)
        assert reg.get_by_name("int_width_byte").fires(byte_w) is True
        assert reg.get_by_name("int_width_byte").fires(w) is False
        assert reg.get_by_name("int_width_byte").fires(AstNil()) is False
        assert reg.get_by_name("int_width_large").fires(big_w) is True
        assert reg.get_by_name("int_width_large").fires(byte_w) is False
        assert reg.get_by_name("int_width_large").fires(AstNil()) is False

    def test_int_registry_extends_existing(self):
        base = DiscriminatorRegistry()
        before = len(base)
        make_int_registry(base)
        assert len(base) > before

    def test_end_to_end_int_observations_differ(self):
        """Gate G1 under Phase 4a: walker + adapter unchanged, yet
        integer-sensitive observations split x=1 from x=2."""
        reg = make_structural_registry()
        make_int_registry(reg)
        classifier = AstClassifier(reg, tuple(d.id for d in reg.all()))

        obs1 = _observe(parse_to_tree("x = 1"), classifier)
        obs2 = _observe(parse_to_tree("x = 2"), classifier)

        # Different programs → different observation sets (the specific
        # IntBit zpaths differ because bit-value is in the coordinate).
        assert obs1 != obs2

    def test_end_to_end_int_observations_idempotent(self):
        """Parsing the same program twice yields identical observations."""
        reg = make_structural_registry()
        make_int_registry(reg)
        classifier = AstClassifier(reg, tuple(d.id for d in reg.all()))
        assert (_observe(parse_to_tree("x = 42"), classifier)
                == _observe(parse_to_tree("x = 42"), classifier))


def _build_int_root_zero():
    """Parse `x = 0` and extract its IntRoot for inspection."""
    return _find_int_root(parse_to_tree("x = 0"))


def _observe(tree, classifier):
    """Collect (zpath, discriminator) observations from walking `tree`."""
    patch = Patch()
    emit_patch(walk(tree, classifier, ast_children, key_fn=ast_key), patch)
    return {(o.element, o.discriminator, o.result) for o in patch.observations}
