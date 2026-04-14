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
    TAG_NIL, TAG_SCALAR, TAG_FIELD, TAG_LIST_SEG, TAG_NODE_WRAP,
    SLOT_NAME, SLOT_DIRECT_VALUE, SLOT_LIST_OFFSET,
    AstNil, AstScalar, AstField, AstListSeg, AstNodeWrap,
    AstClassifier,
    ast_key, ast_children,
    parse_to_tree, module_to_tree,
    make_structural_registry, make_category_registry,
    make_ast_class_registry, make_field_registry,
    make_scalar_kind_registry, make_list_registry,
    make_naming_registry,
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
        assert ast_key(s) == (morton2(0, 1) << 3) | TAG_SCALAR

    def test_field_key_from_parent_and_ordinal(self):
        ns = AstScalar(kind="field_name", subkind="str", value="x",
                        parent_key=0, ordinal=SLOT_NAME)
        f = AstField(parent_key=42, field_ordinal=3,
                      name_scalar=ns, value=AstNil())
        assert ast_key(f) == (morton2(42, 3) << 3) | TAG_FIELD

    def test_listseg_key_from_nested_morton(self):
        s = AstListSeg(parent_key=100, lo=4, length=8,
                        left=AstNil(), right=AstNil())
        q = morton2(4, 8)
        assert ast_key(s) == (morton2(100, q) << 3) | TAG_LIST_SEG

    def test_nodewrap_key_from_parent_and_ordinal(self):
        w = AstNodeWrap(ast_class="Module", kind_bucket="statement",
                         parent_key=0, ordinal=0, fields_root=AstNil())
        assert ast_key(w) == (morton2(0, 0) << 3) | TAG_NODE_WRAP


# ---------------------------------------------------------------------------
# Gate G2: every constructor is discriminable (tag disjointness)
# ---------------------------------------------------------------------------


class TestG2TagDisjointness:
    def test_distinct_tags(self):
        assert len({TAG_NIL, TAG_SCALAR, TAG_FIELD, TAG_LIST_SEG,
                     TAG_NODE_WRAP}) == 5

    def test_tags_fit_in_3_bits(self):
        for tag in (TAG_NIL, TAG_SCALAR, TAG_FIELD, TAG_LIST_SEG,
                     TAG_NODE_WRAP):
            assert 0 <= tag < 8

    def test_keys_separable_by_tag(self):
        """Different constructors at the same coordinate give distinct keys."""
        pk, o = 7, 3
        s = AstScalar(kind="int", subkind="int", value=0,
                       parent_key=pk, ordinal=o)
        w = AstNodeWrap(ast_class="X", kind_bucket="other",
                         parent_key=pk, ordinal=o, fields_root=AstNil())
        assert ast_key(s) != ast_key(w)
        # Low 3 bits differ by tag
        assert ast_key(s) & 0b111 == TAG_SCALAR
        assert ast_key(w) & 0b111 == TAG_NODE_WRAP


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
        Bool/int/float/str/bytes are observed normally.
        """
        tree = parse_to_tree("True; 1; 1.5; 'x'; b'y'")
        kinds = _collect_scalar_kinds(tree)
        for k in ("int", "float", "str", "bool", "bytes"):
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
