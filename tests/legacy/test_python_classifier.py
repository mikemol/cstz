"""Tests for cstz.python_classifier — type inference, κ-classification, factorize."""
from __future__ import annotations

import ast
import tempfile
from pathlib import Path
from typing import Optional

import pytest
from cstz.legacy.python_classifier import (
    _Env, _infer, _classify_kappa, _extract_params, _receiver_domain,
    _build_sppf, factorize, _KNOWN_TYPES, _PARAM_TYPES,
)
from cstz.legacy.core import SPPF


# ── _Env ─────────────────────────────────────────────────────────────

class TestEnv:
    def test_bind_and_get(self) -> None:
        env = _Env()
        env.bind("x", "int")
        assert env.get("x") == "int"

    def test_get_from_parent(self) -> None:
        parent = _Env()
        parent.bind("x", "str")
        child = parent.child()
        assert child.get("x") == "str"

    def test_get_from_known_types(self) -> None:
        env = _Env()
        assert env.get("Graph") == "Graph"

    def test_get_missing(self) -> None:
        env = _Env()
        assert env.get("nonexistent") is None

    def test_child_shadows_parent(self) -> None:
        parent = _Env()
        parent.bind("x", "int")
        child = parent.child()
        child.bind("x", "str")
        assert child.get("x") == "str"
        assert parent.get("x") == "int"

    def test_get_no_parent_no_known(self) -> None:
        env = _Env()
        assert env.get("zzz_unknown_zzz") is None


# ── _infer ───────────────────────────────────────────────────────────

def _parse_expr(code: str) -> ast.expr:
    return ast.parse(code, mode='eval').body


def _env_with_known() -> _Env:
    env = _Env()
    for k, v in _KNOWN_TYPES.items():
        env.bind(k, v)
    return env


class TestInfer:
    def test_name(self) -> None:
        env = _Env()
        env.bind("x", "int")
        node = _parse_expr("x")
        assert _infer(node, env) == "int"

    def test_name_unknown(self) -> None:
        env = _Env()
        assert _infer(_parse_expr("unknown_var"), env) is None

    def test_attribute_with_recv_attr(self) -> None:
        env = _env_with_known()
        node = _parse_expr("RDF.type")
        assert _infer(node, env) == "URIRef"

    def test_attribute_with_wildcard(self) -> None:
        env = _Env()
        env.bind("ns", "NS")
        node = _parse_expr("ns.something")
        assert _infer(node, env) == "URIRef"

    def test_attribute_generic(self) -> None:
        env = _Env()
        env.bind("obj", "MyClass")
        node = _parse_expr("obj.method")
        assert _infer(node, env) == "MyClass.method"

    def test_attribute_no_receiver(self) -> None:
        env = _Env()
        node = _parse_expr("unknown.attr")
        assert _infer(node, env) is None

    def test_call_arrow_type(self) -> None:
        env = _env_with_known()
        node = _parse_expr("len([1,2,3])")
        assert _infer(node, env) == "int"

    def test_call_method_ret(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_expr("g.parse('x')")
        assert _infer(node, env) == "Graph"

    def test_call_no_type(self) -> None:
        env = _Env()
        node = _parse_expr("unknown_func()")
        assert _infer(node, env) is None

    def test_call_non_arrow_non_method(self) -> None:
        env = _Env()
        env.bind("f", "SomeType")
        node = _parse_expr("f()")
        assert _infer(node, env) is None

    def test_constant_none(self) -> None:
        assert _infer(_parse_expr("None"), _Env()) == "NoneType"

    def test_constant_bool(self) -> None:
        assert _infer(_parse_expr("True"), _Env()) == "bool"

    def test_constant_int(self) -> None:
        assert _infer(_parse_expr("42"), _Env()) == "int"

    def test_constant_float(self) -> None:
        assert _infer(_parse_expr("3.14"), _Env()) == "float"

    def test_constant_str(self) -> None:
        assert _infer(_parse_expr("'hello'"), _Env()) == "str"

    def test_constant_other(self) -> None:
        assert _infer(_parse_expr("b'bytes'"), _Env()) is None

    def test_list(self) -> None:
        assert _infer(_parse_expr("[1,2]"), _Env()) == "list"

    def test_dict(self) -> None:
        assert _infer(_parse_expr("{}"), _Env()) == "dict"

    def test_set(self) -> None:
        assert _infer(_parse_expr("{1,2}"), _Env()) == "set"

    def test_tuple(self) -> None:
        assert _infer(_parse_expr("(1,2)"), _Env()) == "tuple"

    def test_fstring(self) -> None:
        assert _infer(_parse_expr("f'x={1}'"), _Env()) == "str"

    def test_unsupported_node(self) -> None:
        node = _parse_expr("1 + 2")
        assert _infer(node, _Env()) is None

    def test_call_method_in_method_ret_no_dot(self) -> None:
        """Call where ft has no dot and is not an arrow."""
        env = _Env()
        env.bind("f", "int")
        node = _parse_expr("f()")
        assert _infer(node, env) is None

    def test_call_method_dot_not_in_method_ret(self) -> None:
        """Call where ft has a dot but method not in _METHOD_RET."""
        env = _Env()
        env.bind("obj", "MyClass")
        node = _parse_expr("obj.unknown_method()")
        assert _infer(node, env) is None


# ── _receiver_domain ─────────────────────────────────────────────────

class TestReceiverDomain:
    @pytest.mark.parametrize("rt,expected", [
        (None, "?"),
        ("Graph", "graph"),
        ("MyGraph", "graph"),
        ("Self", "state"),
        ("Self.x", "state"),
        ("Kernel", "kernel"),
        ("KernelFoo", "kernel"),
        ("AST", "syntax"),
        ("ast", "syntax"),
        ("ASTNode", "syntax"),
        ("str", "string"),
        ("bytes", "string"),
        ("str.upper", "string"),
        ("list", "sequence"),
        ("tuple", "sequence"),
        ("list.append", "sequence"),
        ("tuple.count", "sequence"),
        ("dict", "mapping"),
        ("dict.get", "mapping"),
        ("set", "collection"),
        ("frozenset", "collection"),
        ("set.add", "collection"),
        ("int", "scalar"),
        ("float", "scalar"),
        ("bool", "scalar"),
        ("NoneType", "scalar"),
        ("→int", "arrow"),
        ("SomeObject", "object"),
    ])
    def test_domain(self, rt: Optional[str], expected: str) -> None:
        assert _receiver_domain(rt) == expected


# ── _classify_kappa ──────────────────────────────────────────────────

def _parse_stmt(code: str) -> ast.stmt:
    return ast.parse(code).body[0]


def _parse_single_expr(code: str) -> ast.expr:
    """Parse an expression statement and return the expression."""
    stmt = _parse_stmt(code)
    assert isinstance(stmt, ast.Expr)
    return stmt.value


class TestClassifyKappa:
    def test_constant(self) -> None:
        node = _parse_expr("42")
        assert _classify_kappa(node, _Env()) == "terminal"

    def test_name_store(self) -> None:
        stmt = _parse_stmt("x = 1")
        assert isinstance(stmt, ast.Assign)
        target = stmt.targets[0]
        assert _classify_kappa(target, _Env()) == "bind"

    def test_name_arrow(self) -> None:
        env = _Env()
        env.bind("f", "→int")
        node = _parse_expr("f")
        assert _classify_kappa(node, env) == "arrow"

    def test_name_var(self) -> None:
        env = _Env()
        env.bind("x", "int")
        node = _parse_expr("x")
        assert _classify_kappa(node, env) == "var"

    def test_name_no_type(self) -> None:
        node = _parse_expr("x")
        assert _classify_kappa(node, _Env()) == "var"

    def test_attr_representable(self) -> None:
        env = _env_with_known()
        node = _parse_expr("RDF.type")
        assert _classify_kappa(node, env) == "representable"

    def test_attr_add(self) -> None:
        env = _Env()
        env.bind("s", "set")
        node = _parse_expr("s.add")
        assert _classify_kappa(node, env) == "monoid.op@collection"

    def test_attr_remove(self) -> None:
        env = _Env()
        env.bind("s", "set")
        node = _parse_expr("s.remove")
        assert _classify_kappa(node, env) == "monoid.op@collection"

    def test_attr_append(self) -> None:
        env = _Env()
        env.bind("lst", "list")
        node = _parse_expr("lst.append")
        assert _classify_kappa(node, env) == "free_monoid.op@sequence"

    def test_attr_extend(self) -> None:
        env = _Env()
        env.bind("lst", "list")
        node = _parse_expr("lst.extend")
        assert _classify_kappa(node, env) == "free_monoid.op@sequence"

    def test_attr_objects(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_expr("g.objects")
        assert _classify_kappa(node, env) == "pullback@graph"

    def test_attr_subjects(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_expr("g.subjects")
        assert _classify_kappa(node, env) == "pullback@graph"

    def test_attr_triples(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_expr("g.triples")
        assert _classify_kappa(node, env) == "pullback@graph"

    def test_attr_predicate_objects(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_expr("g.predicate_objects")
        assert _classify_kappa(node, env) == "pullback@graph"

    def test_attr_subject_predicates(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_expr("g.subject_predicates")
        assert _classify_kappa(node, env) == "pullback@graph"

    def test_attr_query(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_expr("g.query")
        assert _classify_kappa(node, env) == "image@graph"

    def test_attr_startswith(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_expr("s.startswith")
        assert _classify_kappa(node, env) == "subobject"

    def test_attr_endswith(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_expr("s.endswith")
        assert _classify_kappa(node, env) == "subobject"

    def test_attr_contains(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_expr("s.__contains__")
        assert _classify_kappa(node, env) == "subobject"

    def test_attr_split(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_expr("s.split")
        assert _classify_kappa(node, env) == "coproduct"

    def test_attr_rsplit(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_expr("s.rsplit")
        assert _classify_kappa(node, env) == "coproduct"

    def test_attr_join(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_expr("s.join")
        assert _classify_kappa(node, env) == "free_monoid.fold"

    def test_attr_items(self) -> None:
        env = _Env()
        env.bind("d", "dict")
        node = _parse_expr("d.items")
        assert _classify_kappa(node, env) == "projection@mapping"

    def test_attr_keys(self) -> None:
        env = _Env()
        env.bind("d", "dict")
        node = _parse_expr("d.keys")
        assert _classify_kappa(node, env) == "projection@mapping"

    def test_attr_values(self) -> None:
        env = _Env()
        env.bind("d", "dict")
        node = _parse_expr("d.values")
        assert _classify_kappa(node, env) == "projection@mapping"

    def test_attr_get(self) -> None:
        env = _Env()
        env.bind("d", "dict")
        node = _parse_expr("d.get")
        assert _classify_kappa(node, env) == "partial@mapping"

    def test_attr_type(self) -> None:
        env = _Env()
        env.bind("obj", "SomeClass")
        node = _parse_expr("obj.type")
        assert _classify_kappa(node, env) == "classifier"

    def test_attr_generic(self) -> None:
        env = _Env()
        env.bind("obj", "SomeClass")
        node = _parse_expr("obj.foo")
        assert _classify_kappa(node, env) == "morphism@object"

    # ── Call classifications ──
    def test_call_isinstance(self) -> None:
        node = _parse_single_expr("isinstance(x, int)")
        assert _classify_kappa(node, _env_with_known()) == "fiber"

    def test_call_set(self) -> None:
        node = _parse_single_expr("set()")
        assert _classify_kappa(node, _env_with_known()) == "powerset"

    def test_call_dict(self) -> None:
        node = _parse_single_expr("dict()")
        assert _classify_kappa(node, _env_with_known()) == "exponential"

    def test_call_list(self) -> None:
        node = _parse_single_expr("list()")
        assert _classify_kappa(node, _env_with_known()) == "free_monoid"

    def test_call_sorted(self) -> None:
        node = _parse_single_expr("sorted([])")
        assert _classify_kappa(node, _env_with_known()) == "total_order"

    def test_call_len(self) -> None:
        node = _parse_single_expr("len([])")
        assert _classify_kappa(node, _env_with_known()) == "cardinality"

    def test_call_next(self) -> None:
        node = _parse_single_expr("next(iter([]))")
        assert _classify_kappa(node, _env_with_known()) == "unit"

    def test_call_print(self) -> None:
        node = _parse_single_expr("print('hi')")
        assert _classify_kappa(node, _env_with_known()) == "effect"

    def test_call_str_coerce(self) -> None:
        node = _parse_single_expr("str(42)")
        assert _classify_kappa(node, _env_with_known()) == "coerce"

    def test_call_int_coerce(self) -> None:
        node = _parse_single_expr("int('1')")
        assert _classify_kappa(node, _env_with_known()) == "coerce"

    def test_call_float_coerce(self) -> None:
        node = _parse_single_expr("float('1.0')")
        assert _classify_kappa(node, _env_with_known()) == "coerce"

    def test_call_bool_coerce(self) -> None:
        node = _parse_single_expr("bool(0)")
        assert _classify_kappa(node, _env_with_known()) == "coerce"

    def test_call_uriref(self) -> None:
        node = _parse_single_expr("URIRef('x')")
        assert _classify_kappa(node, _env_with_known()) == "inject"

    def test_call_bnode(self) -> None:
        node = _parse_single_expr("BNode()")
        assert _classify_kappa(node, _env_with_known()) == "inject"

    def test_call_literal(self) -> None:
        node = _parse_single_expr("Literal('x')")
        assert _classify_kappa(node, _env_with_known()) == "inject"

    def test_call_namespace(self) -> None:
        node = _parse_single_expr("Namespace('x')")
        assert _classify_kappa(node, _env_with_known()) == "representable.new"

    def test_call_hasattr(self) -> None:
        node = _parse_single_expr("hasattr(x, 'y')")
        assert _classify_kappa(node, _env_with_known()) == "subobject"

    def test_call_getattr(self) -> None:
        node = _parse_single_expr("getattr(x, 'y')")
        assert _classify_kappa(node, _env_with_known()) == "eval"

    def test_call_generic(self) -> None:
        node = _parse_single_expr("unknown_func()")
        assert _classify_kappa(node, _Env()) == "apply"

    def test_call_method_unrecognized(self) -> None:
        """Method call with unrecognized attr → falls through all
        checks to return 'apply'."""
        env = _Env()
        env.bind("obj", "SomeClass")
        node = _parse_single_expr("obj.frobnicate()")
        assert _classify_kappa(node, env) == "apply"

    # Method call κ-tags
    def test_call_method_add_graph(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_single_expr("g.add((s,p,o))")
        assert _classify_kappa(node, env) == "graph.emit"

    def test_call_method_add_set(self) -> None:
        env = _Env()
        env.bind("s", "set")
        node = _parse_single_expr("s.add(1)")
        assert _classify_kappa(node, env) == "powerset.insert"

    def test_call_method_add_other(self) -> None:
        env = _Env()
        env.bind("obj", "SomeClass")
        node = _parse_single_expr("obj.add(1)")
        assert _classify_kappa(node, env) == "monoid.op@object"

    def test_call_method_add_no_receiver(self) -> None:
        env = _Env()
        node = _parse_single_expr("unknown.add(1)")
        assert _classify_kappa(node, env) == "monoid.op@?"

    def test_call_method_append(self) -> None:
        env = _Env()
        env.bind("lst", "list")
        node = _parse_single_expr("lst.append(1)")
        assert _classify_kappa(node, env) == "free_monoid.snoc@sequence"

    def test_call_method_objects(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_single_expr("g.objects()")
        assert _classify_kappa(node, env) == "pullback.query@graph"

    def test_call_method_subjects(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_single_expr("g.subjects()")
        assert _classify_kappa(node, env) == "pullback.query@graph"

    def test_call_method_triples(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_single_expr("g.triples(())")
        assert _classify_kappa(node, env) == "pullback.query@graph"

    def test_call_method_query(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_single_expr("g.query('SELECT ?s')")
        assert _classify_kappa(node, env) == "image.compute@graph"

    def test_call_method_parse(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_single_expr("g.parse('data')")
        assert _classify_kappa(node, env) == "left_adjoint"

    def test_call_method_bind(self) -> None:
        env = _Env()
        env.bind("g", "Graph")
        node = _parse_single_expr("g.bind('ns', 'uri')")
        assert _classify_kappa(node, env) == "equip"

    def test_call_method_startswith(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_single_expr("s.startswith('x')")
        assert _classify_kappa(node, env) == "subobject.test"

    def test_call_method_endswith(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_single_expr("s.endswith('x')")
        assert _classify_kappa(node, env) == "subobject.test"

    def test_call_method_join(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_single_expr("s.join(['a'])")
        assert _classify_kappa(node, env) == "free_monoid.fold"

    def test_call_method_split(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_single_expr("s.split(',')")
        assert _classify_kappa(node, env) == "coproduct.decompose"

    def test_call_method_rsplit(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_single_expr("s.rsplit(',')")
        assert _classify_kappa(node, env) == "coproduct.decompose"

    def test_call_method_get(self) -> None:
        env = _Env()
        env.bind("d", "dict")
        node = _parse_single_expr("d.get('k')")
        assert _classify_kappa(node, env) == "partial.apply@mapping"

    def test_call_method_items(self) -> None:
        env = _Env()
        env.bind("d", "dict")
        node = _parse_single_expr("d.items()")
        assert _classify_kappa(node, env) == "projection.compute@mapping"

    def test_call_method_keys(self) -> None:
        env = _Env()
        env.bind("d", "dict")
        node = _parse_single_expr("d.keys()")
        assert _classify_kappa(node, env) == "projection.compute@mapping"

    def test_call_method_values(self) -> None:
        env = _Env()
        env.bind("d", "dict")
        node = _parse_single_expr("d.values()")
        assert _classify_kappa(node, env) == "projection.compute@mapping"

    def test_call_method_format(self) -> None:
        env = _Env()
        env.bind("s", "str")
        node = _parse_single_expr("s.format()")
        assert _classify_kappa(node, env) == "free_monoid.fold"

    # ── Statement classifications ──
    def test_assign(self) -> None:
        node = _parse_stmt("x = 1")
        assert _classify_kappa(node, _Env()) == "let"

    def test_augassign(self) -> None:
        node = _parse_stmt("x += 1")
        assert _classify_kappa(node, _Env()) == "monoid.accum"

    def test_for(self) -> None:
        node = _parse_stmt("for x in y: pass")
        assert _classify_kappa(node, _Env()) == "fold"

    def test_while(self) -> None:
        node = _parse_stmt("while True: pass")
        assert _classify_kappa(node, _Env()) == "fixpoint"

    def test_if_isinstance(self) -> None:
        node = _parse_stmt("if isinstance(x, int): pass")
        assert _classify_kappa(node, _env_with_known()) == "coproduct.elim"

    def test_if_compare(self) -> None:
        node = _parse_stmt("if x == 1: pass")
        assert _classify_kappa(node, _Env()) == "equalizer"

    def test_if_not(self) -> None:
        node = _parse_stmt("if not x: pass")
        assert _classify_kappa(node, _Env()) == "complement"

    def test_if_call_attr_func(self) -> None:
        """If test is a Call but func is Attribute, not Name."""
        node = _parse_stmt("if obj.method(): pass")
        assert _classify_kappa(node, _Env()) == "coproduct.elim"

    def test_if_call_name_not_isinstance(self) -> None:
        """If test is Call with Name func, but name != isinstance."""
        env = _env_with_known()
        node = _parse_stmt("if len(x): pass")
        assert _classify_kappa(node, env) == "coproduct.elim"

    def test_if_unaryop_not_not(self) -> None:
        """If test is UnaryOp but op is USub (not Not) → coproduct.elim."""
        node = _parse_stmt("if -x: pass")
        assert _classify_kappa(node, _Env()) == "coproduct.elim"

    def test_if_unaryop_bitnot(self) -> None:
        """If test is UnaryOp(Invert) — another non-Not unary op."""
        node = _parse_stmt("if ~x: pass")
        assert _classify_kappa(node, _Env()) == "coproduct.elim"

    def test_if_generic(self) -> None:
        node = _parse_stmt("if x: pass")
        assert _classify_kappa(node, _Env()) == "coproduct.elim"

    def test_return(self) -> None:
        tree = ast.parse("def f():\n  return 1")
        func = tree.body[0]
        assert isinstance(func, ast.FunctionDef)
        ret = func.body[0]
        assert _classify_kappa(ret, _Env()) == "terminal.map"

    def test_tuple_load(self) -> None:
        node = _parse_expr("(1, 2)")
        assert _classify_kappa(node, _Env()) == "product"

    def test_tuple_store(self) -> None:
        stmt = _parse_stmt("a, b = 1, 2")
        assert isinstance(stmt, ast.Assign)
        target = stmt.targets[0]
        assert _classify_kappa(target, _Env()) == "product.unpack"

    def test_list_literal(self) -> None:
        node = _parse_expr("[1, 2]")
        assert _classify_kappa(node, _Env()) == "free_monoid.literal"

    def test_dict_literal(self) -> None:
        node = _parse_expr("{'a': 1}")
        assert _classify_kappa(node, _Env()) == "exponential.literal"

    def test_set_literal(self) -> None:
        node = _parse_expr("{1, 2}")
        assert _classify_kappa(node, _Env()) == "powerset.literal"

    def test_listcomp(self) -> None:
        node = _parse_expr("[x for x in y]")
        assert _classify_kappa(node, _Env()) == "free_monoid.map"

    def test_setcomp(self) -> None:
        node = _parse_expr("{x for x in y}")
        assert _classify_kappa(node, _Env()) == "powerset.map"

    def test_dictcomp(self) -> None:
        node = _parse_expr("{k: v for k, v in items}")
        assert _classify_kappa(node, _Env()) == "exponential.map"

    def test_generatorexp(self) -> None:
        node = _parse_expr("(x for x in y)")
        assert _classify_kappa(node, _Env()) == "lazy_fold"

    def test_boolop_and(self) -> None:
        node = _parse_expr("a and b")
        assert _classify_kappa(node, _Env()) == "meet"

    def test_boolop_or(self) -> None:
        node = _parse_expr("a or b")
        assert _classify_kappa(node, _Env()) == "join"

    def test_compare(self) -> None:
        node = _parse_expr("a == b")
        assert _classify_kappa(node, _Env()) == "equalizer"

    def test_binop_add(self) -> None:
        node = _parse_expr("a + b")
        assert _classify_kappa(node, _Env()) == "monoid.op"

    def test_binop_mod(self) -> None:
        node = _parse_expr("a % b")
        assert _classify_kappa(node, _Env()) == "quotient"

    def test_binop_other(self) -> None:
        node = _parse_expr("a * b")
        assert _classify_kappa(node, _Env()) == "bimap"

    def test_unaryop_not(self) -> None:
        node = _parse_expr("not x")
        assert _classify_kappa(node, _Env()) == "complement"

    def test_unaryop_neg(self) -> None:
        node = _parse_expr("-x")
        assert _classify_kappa(node, _Env()) == "endomorphism"

    def test_fstring(self) -> None:
        node = _parse_expr("f'hello {x}'")
        assert _classify_kappa(node, _Env()) == "free_monoid.fold"

    def test_formattedvalue(self) -> None:
        fstr = _parse_expr("f'{x}'")
        assert isinstance(fstr, ast.JoinedStr)
        fv = fstr.values[0]
        assert isinstance(fv, ast.FormattedValue)
        assert _classify_kappa(fv, _Env()) == "coerce"

    def test_functiondef(self) -> None:
        node = _parse_stmt("def f(): pass")
        assert _classify_kappa(node, _Env()) == "exponential.intro"

    def test_async_functiondef(self) -> None:
        node = _parse_stmt("async def f(): pass")
        assert _classify_kappa(node, _Env()) == "exponential.intro"

    def test_classdef(self) -> None:
        node = _parse_stmt("class C: pass")
        assert _classify_kappa(node, _Env()) == "classifier.intro"

    def test_importfrom(self) -> None:
        node = _parse_stmt("from os import path")
        assert _classify_kappa(node, _Env()) == "pullback.import"

    def test_expr_stmt(self) -> None:
        node = _parse_stmt("foo()")
        assert _classify_kappa(node, _Env()) == "effect.seq"

    def test_raise(self) -> None:
        node = _parse_stmt("raise ValueError()")
        assert _classify_kappa(node, _Env()) == "initial"

    def test_try(self) -> None:
        node = _parse_stmt("try:\n  pass\nexcept:\n  pass")
        assert _classify_kappa(node, _Env()) == "coproduct.handle"

    def test_with(self) -> None:
        node = _parse_stmt("with open('f'): pass")
        assert _classify_kappa(node, _Env()) == "monad.bind"

    def test_yield(self) -> None:
        tree = ast.parse("def f():\n  yield 1")
        func = tree.body[0]
        assert isinstance(func, ast.FunctionDef)
        expr_stmt = func.body[0]
        assert isinstance(expr_stmt, ast.Expr)
        assert _classify_kappa(expr_stmt.value, _Env()) == "cofree"

    def test_continue(self) -> None:
        tree = ast.parse("for x in y:\n  continue")
        for_node = tree.body[0]
        assert isinstance(for_node, ast.For)
        assert _classify_kappa(for_node.body[0], _Env()) == "fixpoint.next"

    def test_break(self) -> None:
        tree = ast.parse("for x in y:\n  break")
        for_node = tree.body[0]
        assert isinstance(for_node, ast.For)
        assert _classify_kappa(for_node.body[0], _Env()) == "fixpoint.halt"

    def test_pass(self) -> None:
        node = _parse_stmt("pass")
        assert _classify_kappa(node, _Env()) == "identity"

    def test_fallback(self) -> None:
        """An AST node type not explicitly handled → lowercase name."""
        node = _parse_stmt("del x")
        assert _classify_kappa(node, _Env()) == "delete"


# ── _extract_params ──────────────────────────────────────────────────

class TestExtractParams:
    def test_name(self) -> None:
        node = _parse_expr("x")
        assert _extract_params(node) == (("n", "x"),)

    def test_attribute(self) -> None:
        node = _parse_expr("x.y")
        assert _extract_params(node) == (("a", "y"),)

    def test_functiondef(self) -> None:
        node = _parse_stmt("def foo(): pass")
        assert _extract_params(node) == (("n", "foo"),)

    def test_async_functiondef(self) -> None:
        node = _parse_stmt("async def bar(): pass")
        assert _extract_params(node) == (("n", "bar"),)

    def test_classdef(self) -> None:
        node = _parse_stmt("class MyClass: pass")
        assert _extract_params(node) == (("n", "MyClass"),)

    def test_constant_short(self) -> None:
        node = _parse_expr("42")
        assert _extract_params(node) == (("v", "42"),)

    def test_constant_long(self) -> None:
        node = _parse_expr("'x' * 100")
        # This is a BinOp, not a Constant — need actual long constant
        long_code = repr("a" * 100)
        node = _parse_expr(long_code)
        p = dict(_extract_params(node))
        assert "v" in p
        assert len(p["v"]) <= 80  # Hashed to 12 chars

    def test_arg(self) -> None:
        tree = ast.parse("def f(x): pass")
        func = tree.body[0]
        assert isinstance(func, ast.FunctionDef)
        arg = func.args.args[0]
        assert _extract_params(arg) == (("n", "x"),)

    def test_alias(self) -> None:
        tree = ast.parse("from os import path")
        imp = tree.body[0]
        assert isinstance(imp, ast.ImportFrom)
        alias = imp.names[0]
        assert _extract_params(alias) == (("n", "path"),)

    def test_importfrom(self) -> None:
        node = _parse_stmt("from os.path import join")
        assert _extract_params(node) == (("m", "os.path"),)

    def test_importfrom_no_module(self) -> None:
        """Relative import with no module name."""
        node = _parse_stmt("from . import foo")
        p = dict(_extract_params(node))
        assert p["m"] == ""

    def test_keyword_with_arg(self) -> None:
        call = _parse_single_expr("f(key='val')")
        assert isinstance(call, ast.Call)
        kw = call.keywords[0]
        assert _extract_params(kw) == (("n", "key"),)

    def test_keyword_no_arg(self) -> None:
        """**kwargs expansion → keyword.arg is None."""
        call = _parse_single_expr("f(**d)")
        assert isinstance(call, ast.Call)
        kw = call.keywords[0]
        assert _extract_params(kw) == ()

    def test_no_params(self) -> None:
        """A node type with no special extraction → empty tuple."""
        node = _parse_expr("a + b")
        assert _extract_params(node) == ()


# ── _build_sppf special paths ───────────────────────────────────────

class TestBuildSPPF:
    def test_functiondef_with_known_param(self) -> None:
        """FunctionDef with param in _PARAM_TYPES creates child env."""
        sppf = SPPF()
        env = _env_with_known()
        tree = ast.parse("def f(g): return g")
        _build_sppf(tree.body[0], sppf, env)
        assert sppf.node_count > 0

    def test_classdef_child_env(self) -> None:
        sppf = SPPF()
        env = _env_with_known()
        tree = ast.parse("class C:\n  x = 1")
        _build_sppf(tree.body[0], sppf, env)

    def test_importfrom_known_binding(self) -> None:
        sppf = SPPF()
        env = _env_with_known()
        tree = ast.parse("from rdflib import Graph")
        _build_sppf(tree.body[0], sppf, env)
        assert env.get("Graph") == "Graph"

    def test_assign_type_tracking(self) -> None:
        sppf = SPPF()
        env = _env_with_known()
        tree = ast.parse("x = 42")
        _build_sppf(tree.body[0], sppf, env)
        assert env.get("x") == "int"

    def test_assign_no_type(self) -> None:
        sppf = SPPF()
        env = _Env()
        tree = ast.parse("x = unknown_var")
        _build_sppf(tree.body[0], sppf, env)
        # x should not be bound since unknown_var has no type
        assert env.get("x") is None

    def test_assign_multi_target(self) -> None:
        """Multi-target assign doesn't trigger type binding."""
        sppf = SPPF()
        env = _env_with_known()
        tree = ast.parse("a = b = 1")
        _build_sppf(tree.body[0], sppf, env)

    def test_importfrom_with_alias(self) -> None:
        sppf = SPPF()
        env = _env_with_known()
        tree = ast.parse("from rdflib import Graph as G")
        _build_sppf(tree.body[0], sppf, env)

    def test_importfrom_unknown_name(self) -> None:
        sppf = SPPF()
        env = _Env()
        tree = ast.parse("from os import getcwd")
        _build_sppf(tree.body[0], sppf, env)

    def test_functiondef_unknown_param(self) -> None:
        """Param not in _PARAM_TYPES → no binding."""
        sppf = SPPF()
        env = _env_with_known()
        tree = ast.parse("def f(zzz): pass")
        _build_sppf(tree.body[0], sppf, env)

    def test_importfrom_no_names(self) -> None:
        """ImportFrom with empty names list."""
        sppf = SPPF()
        env = _Env()
        node = ast.ImportFrom(module="os", names=[], level=0)
        ast.fix_missing_locations(node)
        _build_sppf(node, sppf, env)


# ── factorize ────────────────────────────────────────────────────────

class TestFactorize:
    def test_source_text(self) -> None:
        sppf = factorize("x = 1")
        assert sppf.node_count > 0

    def test_ast_module(self) -> None:
        tree = ast.parse("x = 1")
        sppf = factorize(tree)
        assert sppf.node_count > 0

    def test_file(self, tmp_path: Path) -> None:
        f = tmp_path / "test.py"
        f.write_text("x = 1\n")
        sppf = factorize(f)
        assert sppf.node_count > 0

    def test_file_str_path(self, tmp_path: Path) -> None:
        f = tmp_path / "test.py"
        f.write_text("y = 2\n")
        sppf = factorize(str(f))
        assert sppf.node_count > 0

    def test_directory(self, tmp_path: Path) -> None:
        f1 = tmp_path / "a.py"
        f1.write_text("x = 1\n")
        f2 = tmp_path / "b.py"
        f2.write_text("y = 2\n")
        # __init__.py should be skipped
        init = tmp_path / "__init__.py"
        init.write_text("# init")
        sppf = factorize(tmp_path)
        assert sppf.node_count > 0

    def test_directory_with_syntax_error(self, tmp_path: Path) -> None:
        good = tmp_path / "good.py"
        good.write_text("x = 1\n")
        bad = tmp_path / "bad.py"
        bad.write_text("def :\n")
        sppf = factorize(tmp_path)
        assert sppf.node_count > 0

    def test_directory_with_unicode_error(self, tmp_path: Path) -> None:
        good = tmp_path / "good.py"
        good.write_text("x = 1\n")
        bad = tmp_path / "bad.py"
        bad.write_bytes(b'\x80\x81\x82')
        sppf = factorize(tmp_path)
        assert sppf.node_count > 0

    def test_extra_types(self) -> None:
        sppf = factorize("x = myobj", extra_types={"myobj": "CustomType"})
        assert sppf.node_count > 0

    def test_path_object(self, tmp_path: Path) -> None:
        f = tmp_path / "test.py"
        f.write_text("x = 1\n")
        sppf = factorize(Path(f))
        assert sppf.node_count > 0

    def test_source_text_fallthrough(self) -> None:
        """String that's not an existing file → treated as source text."""
        sppf = factorize("a = 1\nb = 2")
        assert sppf.node_count > 0

    def test_nested_directory(self, tmp_path: Path) -> None:
        sub = tmp_path / "sub"
        sub.mkdir()
        f = sub / "mod.py"
        f.write_text("z = 3\n")
        sppf = factorize(tmp_path)
        assert sppf.node_count > 0
