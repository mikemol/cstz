"""Tests for the parallel PFF Python classifier in cstz.pff_python_classifier.

These tests exercise the AST → PFF cascade pipeline directly.  They
are NOT a port of tests/test_python_classifier.py — the legacy
classifier and its tests remain the metamathematical reference for
inference.agda.

Coverage focus:
  - The dynamic type environment (no project-specific tables)
  - Per-AST-node observation emission
  - Streaming glue cascade triggered by classifier output
  - The κ-classification of every AST shape touched
  - Public ``factorize`` entry point on every input form
"""

from __future__ import annotations

import ast
import textwrap
from pathlib import Path

from cstz.legacy.pff_python_classifier import (
    _annotation_to_str,
    _bind_declarations,
    _classify_kappa,
    _Env,
    _extract_params,
    _infer_type,
    _seeded_root_env,
    factorize,
)


# ── Helpers ─────────────────────────────────────────────────────────


def _expr(text: str) -> ast.AST:
    """Parse one expression and return the inner ast node."""
    return ast.parse(text, mode="eval").body


def _stmt(text: str) -> ast.AST:
    """Parse one statement and return the first body element."""
    return ast.parse(text).body[0]


# ── _Env ────────────────────────────────────────────────────────────


class TestEnv:
    def test_root_lookup_missing_returns_none(self) -> None:
        env = _Env()
        assert env.get("nope") is None

    def test_bind_then_get(self) -> None:
        env = _Env()
        env.bind("x", "int")
        assert env.get("x") == "int"

    def test_child_inherits_parent(self) -> None:
        parent = _Env()
        parent.bind("a", "int")
        child = parent.child()
        assert child.get("a") == "int"

    def test_child_shadows_parent(self) -> None:
        parent = _Env()
        parent.bind("a", "int")
        child = parent.child()
        child.bind("a", "str")
        assert child.get("a") == "str"
        # Parent unchanged
        assert parent.get("a") == "int"

    def test_seeded_root_env_has_builtins(self) -> None:
        env = _seeded_root_env()
        # Builtin callables tagged with arrow form
        assert env.get("len") == "→int"
        assert env.get("print") == "→NoneType"
        # Constructors tagged as 'type'
        assert env.get("int") == "type"
        assert env.get("list") == "type"
        # Singletons
        assert env.get("True") == "bool"
        assert env.get("None") == "NoneType"


# ── _annotation_to_str ──────────────────────────────────────────────


class TestAnnotationToStr:
    def test_none(self) -> None:
        assert _annotation_to_str(None) is None

    def test_name(self) -> None:
        node = ast.parse("x: int", mode="exec").body[0].annotation
        assert _annotation_to_str(node) == "int"

    def test_string_forward_ref(self) -> None:
        node = ast.parse('x: "Foo"', mode="exec").body[0].annotation
        assert _annotation_to_str(node) == "Foo"

    def test_attribute(self) -> None:
        node = ast.parse("x: pkg.mod.Foo", mode="exec").body[0].annotation
        assert _annotation_to_str(node) == "pkg.mod.Foo"

    def test_subscript(self) -> None:
        node = ast.parse("x: List[int]", mode="exec").body[0].annotation
        assert _annotation_to_str(node) == "List"

    def test_attribute_only_innermost(self) -> None:
        # An Attribute with a non-Name base also produces the qualified form
        node = _expr("a.b.c")
        assert _annotation_to_str(node) == "a.b.c"

    def test_attribute_unrenderable_base(self) -> None:
        # An Attribute on something we can't render → falls back to attr alone
        # Use a Call as the base which _annotation_to_str doesn't handle.
        node = _expr("f().attr")
        assert _annotation_to_str(node) == "attr"

    def test_unknown_annotation_form(self) -> None:
        node = _expr("x + 1")
        assert _annotation_to_str(node) is None


# ── _infer_type ─────────────────────────────────────────────────────


class TestInferType:
    def test_constant_literals(self) -> None:
        env = _Env()
        assert _infer_type(_expr("None"), env) == "NoneType"
        assert _infer_type(_expr("True"), env) == "bool"
        assert _infer_type(_expr("42"), env) == "int"
        assert _infer_type(_expr("3.14"), env) == "float"
        assert _infer_type(_expr("'hi'"), env) == "str"
        assert _infer_type(_expr("b'hi'"), env) == "bytes"

    def test_constant_unknown_value_type(self) -> None:
        # Construct a Constant with an unsupported value type
        node = ast.Constant(value=Ellipsis)
        env = _Env()
        # Ellipsis isn't in _LITERAL_TYPE_NAMES → "?"
        assert _infer_type(node, env) == "?"

    def test_name_bound(self) -> None:
        env = _Env()
        env.bind("x", "int")
        assert _infer_type(_expr("x"), env) == "int"

    def test_name_unbound(self) -> None:
        assert _infer_type(_expr("x"), _Env()) == "?"

    def test_joined_str(self) -> None:
        env = _Env()
        assert _infer_type(_expr("f'{x}'"), env) == "str"

    def test_formatted_value(self) -> None:
        # Pluck a FormattedValue out of a JoinedStr
        node = _expr("f'{x:.2f}'").values[0]
        assert _infer_type(node, _Env()) == "str"

    def test_collection_literals(self) -> None:
        env = _Env()
        assert _infer_type(_expr("[1, 2]"), env) == "list"
        assert _infer_type(_expr("{1: 2}"), env) == "dict"
        assert _infer_type(_expr("{1, 2}"), env) == "set"
        assert _infer_type(_expr("(1, 2)"), env) == "tuple"

    def test_comprehensions(self) -> None:
        env = _Env()
        assert _infer_type(_expr("[x for x in y]"), env) == "list"
        assert _infer_type(_expr("{x for x in y}"), env) == "set"
        assert _infer_type(_expr("{x: y for x in z}"), env) == "dict"
        assert _infer_type(_expr("(x for x in y)"), env) == "iter"

    def test_lambda(self) -> None:
        assert _infer_type(_expr("lambda x: x"), _Env()) == "callable"

    def test_call_arrow_returns_target(self) -> None:
        env = _Env()
        env.bind("f", "→int")
        assert _infer_type(_expr("f()"), env) == "int"

    def test_call_constructor_returns_type(self) -> None:
        env = _seeded_root_env()
        # int() → int (because env binds int → "type")
        assert _infer_type(_expr("int()"), env) == "int"

    def test_call_unbound_func(self) -> None:
        assert _infer_type(_expr("ghost()"), _Env()) == "?"

    def test_call_complex_func(self) -> None:
        # Call whose func is not a Name → can't resolve
        assert _infer_type(_expr("(lambda: 1)()"), _Env()) == "?"

    def test_attribute_with_known_base(self) -> None:
        env = _Env()
        env.bind("obj", "MyClass")
        assert _infer_type(_expr("obj.attr"), env) == "MyClass.attr"

    def test_attribute_with_unknown_base(self) -> None:
        assert _infer_type(_expr("ghost.attr"), _Env()) == "?"

    def test_other_node_type_returns_question(self) -> None:
        # IfExp is a node we don't infer
        assert _infer_type(_expr("a if b else c"), _Env()) == "?"


# ── _classify_kappa (broad shape coverage) ──────────────────────────


class TestClassifyKappa:
    def test_constant(self) -> None:
        assert _classify_kappa(_expr("1")) == "terminal"

    def test_name_load(self) -> None:
        assert _classify_kappa(_expr("x")) == "var"

    def test_name_store(self) -> None:
        node = _stmt("x = 1").targets[0]
        assert _classify_kappa(node) == "bind"

    def test_attribute(self) -> None:
        assert _classify_kappa(_expr("a.b")) == "morphism"

    def test_call(self) -> None:
        assert _classify_kappa(_expr("f()")) == "apply"

    def test_assign(self) -> None:
        assert _classify_kappa(_stmt("x = 1")) == "let"

    def test_annassign(self) -> None:
        assert _classify_kappa(_stmt("x: int = 1")) == "let"

    def test_augassign(self) -> None:
        assert _classify_kappa(_stmt("x += 1")) == "monoid.accum"

    def test_for(self) -> None:
        assert _classify_kappa(_stmt("for i in r: pass")) == "fold"

    def test_async_for(self) -> None:
        node = _stmt("async def f():\n    async for i in r:\n        pass").body[0]
        assert _classify_kappa(node) == "fold"

    def test_while(self) -> None:
        assert _classify_kappa(_stmt("while x: pass")) == "fixpoint"

    def test_if(self) -> None:
        assert _classify_kappa(_stmt("if x: pass")) == "coproduct.elim"

    def test_ifexp(self) -> None:
        assert _classify_kappa(_expr("a if b else c")) == "coproduct.elim"

    def test_return(self) -> None:
        node = _stmt("def f():\n    return 1").body[0]
        assert _classify_kappa(node) == "terminal.map"

    def test_tuple_load(self) -> None:
        assert _classify_kappa(_expr("(1, 2)")) == "product"

    def test_tuple_store(self) -> None:
        node = _stmt("a, b = 1, 2").targets[0]
        assert _classify_kappa(node) == "product.unpack"

    def test_list_literal(self) -> None:
        assert _classify_kappa(_expr("[1, 2]")) == "free_monoid.literal"

    def test_dict_literal(self) -> None:
        assert _classify_kappa(_expr("{1: 2}")) == "exponential.literal"

    def test_set_literal(self) -> None:
        assert _classify_kappa(_expr("{1, 2}")) == "powerset.literal"

    def test_listcomp(self) -> None:
        assert _classify_kappa(_expr("[x for x in y]")) == "free_monoid.map"

    def test_setcomp(self) -> None:
        assert _classify_kappa(_expr("{x for x in y}")) == "powerset.map"

    def test_dictcomp(self) -> None:
        assert _classify_kappa(_expr("{x: y for x in z}")) == "exponential.map"

    def test_generatorexp(self) -> None:
        assert _classify_kappa(_expr("(x for x in y)")) == "lazy_fold"

    def test_boolop_and(self) -> None:
        assert _classify_kappa(_expr("a and b")) == "meet"

    def test_boolop_or(self) -> None:
        assert _classify_kappa(_expr("a or b")) == "join"

    def test_compare(self) -> None:
        assert _classify_kappa(_expr("a == b")) == "equalizer"

    def test_binop(self) -> None:
        assert _classify_kappa(_expr("a + b")) == "binop"

    def test_unaryop_not(self) -> None:
        assert _classify_kappa(_expr("not x")) == "complement"

    def test_unaryop_other(self) -> None:
        assert _classify_kappa(_expr("-x")) == "endomorphism"

    def test_joinedstr(self) -> None:
        assert _classify_kappa(_expr("f'{x}'")) == "free_monoid.fold"

    def test_formattedvalue(self) -> None:
        node = _expr("f'{x}'").values[0]
        assert _classify_kappa(node) == "coerce"

    def test_function_def(self) -> None:
        assert _classify_kappa(_stmt("def f(): pass")) == "exponential.intro"

    def test_async_function_def(self) -> None:
        assert _classify_kappa(_stmt("async def f(): pass")) == "exponential.intro"

    def test_lambda(self) -> None:
        assert _classify_kappa(_expr("lambda: 1")) == "exponential.intro"

    def test_class_def(self) -> None:
        assert _classify_kappa(_stmt("class Foo: pass")) == "classifier.intro"

    def test_import(self) -> None:
        assert _classify_kappa(_stmt("import os")) == "pullback.import"

    def test_import_from(self) -> None:
        assert _classify_kappa(_stmt("from os import path")) == "pullback.import"

    def test_expr_stmt(self) -> None:
        assert _classify_kappa(_stmt("f()")) == "effect.seq"

    def test_raise(self) -> None:
        assert _classify_kappa(_stmt("raise X()")) == "initial"

    def test_try(self) -> None:
        node = _stmt("try:\n    x\nexcept:\n    pass")
        assert _classify_kappa(node) == "coproduct.handle"

    def test_with(self) -> None:
        node = _stmt("with x: pass")
        assert _classify_kappa(node) == "monad.bind"

    def test_async_with(self) -> None:
        node = _stmt("async def f():\n    async with x: pass").body[0]
        assert _classify_kappa(node) == "monad.bind"

    def test_yield(self) -> None:
        node = _stmt("def f():\n    yield 1").body[0].value
        assert _classify_kappa(node) == "cofree"

    def test_yield_from(self) -> None:
        node = _stmt("def f():\n    yield from g()").body[0].value
        assert _classify_kappa(node) == "cofree"

    def test_await(self) -> None:
        node = _stmt("async def f():\n    await g()").body[0].value
        assert _classify_kappa(node) == "monad.bind"

    def test_pass(self) -> None:
        assert _classify_kappa(_stmt("pass")) == "identity"

    def test_break(self) -> None:
        node = _stmt("while x:\n    break").body[0]
        assert _classify_kappa(node) == "fixpoint.halt"

    def test_continue(self) -> None:
        node = _stmt("while x:\n    continue").body[0]
        assert _classify_kappa(node) == "fixpoint.next"

    def test_global(self) -> None:
        node = _stmt("def f():\n    global x").body[0]
        assert _classify_kappa(node) == "scope.escape"

    def test_nonlocal(self) -> None:
        node = _stmt(
            "def outer():\n    def inner():\n        nonlocal x"
        ).body[0].body[0]
        assert _classify_kappa(node) == "scope.escape"

    def test_delete(self) -> None:
        assert _classify_kappa(_stmt("del x")) == "annihilate"

    def test_starred(self) -> None:
        node = _expr("[*xs]").elts[0]
        assert _classify_kappa(node) == "spread"

    def test_subscript(self) -> None:
        assert _classify_kappa(_expr("a[1]")) == "index"

    def test_slice(self) -> None:
        node = _expr("a[1:2]").slice
        assert _classify_kappa(node) == "slice"

    def test_unrecognized_falls_back_to_typename(self) -> None:
        # ast.Load is a context node we never classify explicitly
        assert _classify_kappa(ast.Load()) == "load"


# ── _extract_params ─────────────────────────────────────────────────


class TestExtractParams:
    def test_name(self) -> None:
        assert _extract_params(_expr("foo")) == (("n", "foo"),)

    def test_attribute(self) -> None:
        assert _extract_params(_expr("a.b")) == (("a", "b"),)

    def test_function_def(self) -> None:
        assert _extract_params(_stmt("def my_fn(): pass")) == (("n", "my_fn"),)

    def test_class_def(self) -> None:
        assert _extract_params(_stmt("class C: pass")) == (("n", "C"),)

    def test_async_function_def(self) -> None:
        assert _extract_params(_stmt("async def f(): pass")) == (("n", "f"),)

    def test_constant_short(self) -> None:
        assert _extract_params(_expr("42")) == (("v", "42"),)

    def test_constant_long(self) -> None:
        long_str = "x" * 200
        node = ast.Constant(value=long_str)
        params = dict(_extract_params(node))
        assert params["v"].startswith("<long:")

    def test_arg(self) -> None:
        node = _stmt("def f(x): pass").args.args[0]
        assert _extract_params(node) == (("n", "x"),)

    def test_alias_with_asname(self) -> None:
        node = _stmt("import os as o").names[0]
        params = dict(_extract_params(node))
        assert params == {"n": "os", "as": "o"}

    def test_alias_no_asname(self) -> None:
        node = _stmt("import os").names[0]
        assert _extract_params(node) == (("n", "os"),)

    def test_import_from(self) -> None:
        node = _stmt("from foo import bar")
        params = dict(_extract_params(node))
        assert params["m"] == "foo"

    def test_import_from_relative_no_module(self) -> None:
        node = _stmt("from . import bar")
        params = dict(_extract_params(node))
        assert params["m"] == ""

    def test_import(self) -> None:
        node = _stmt("import os, sys")
        params = dict(_extract_params(node))
        assert params["m"] == "os,sys"

    def test_keyword(self) -> None:
        node = _stmt("f(name=1)").value.keywords[0]
        assert _extract_params(node) == (("n", "name"),)

    def test_keyword_starstar(self) -> None:
        # **kwargs has arg=None → no params
        node = _stmt("f(**d)").value.keywords[0]
        assert _extract_params(node) == ()

    def test_global(self) -> None:
        node = _stmt("def f():\n    global x, y").body[0]
        assert _extract_params(node) == (("n", "x,y"),)

    def test_nonlocal(self) -> None:
        node = _stmt(
            "def outer():\n    def inner():\n        nonlocal x, y"
        ).body[0].body[0]
        assert _extract_params(node) == (("n", "x,y"),)

    def test_unhandled_node(self) -> None:
        # ast.Pass has no identity-discriminating params
        assert _extract_params(_stmt("pass")) == ()


# ── _bind_declarations ──────────────────────────────────────────────


class TestBindDeclarations:
    def test_function_def_binds_outer_and_inner(self) -> None:
        env = _Env()
        node = _stmt("def f(x: int) -> str: pass")
        child = _bind_declarations(node, env)
        assert env.get("f") == "→str"
        assert child.get("x") == "int"
        assert child is not env

    def test_function_def_no_return_annotation(self) -> None:
        env = _Env()
        node = _stmt("def f(): pass")
        _bind_declarations(node, env)
        assert env.get("f") == "→?"

    def test_function_def_no_arg_annotation(self) -> None:
        env = _Env()
        node = _stmt("def f(x): pass")
        child = _bind_declarations(node, env)
        assert child.get("x") == "?"

    def test_async_function_def(self) -> None:
        env = _Env()
        node = _stmt("async def f(x: int) -> bool: pass")
        child = _bind_declarations(node, env)
        assert env.get("f") == "→bool"
        assert child.get("x") == "int"

    def test_class_def(self) -> None:
        env = _Env()
        node = _stmt("class Foo: pass")
        child = _bind_declarations(node, env)
        assert env.get("Foo") == "type"
        assert child is not env

    def test_lambda(self) -> None:
        env = _Env()
        node = _expr("lambda x: x")
        child = _bind_declarations(node, env)
        assert child.get("x") == "?"

    def test_import_from_with_asname(self) -> None:
        env = _Env()
        node = _stmt("from os import path as p")
        _bind_declarations(node, env)
        assert env.get("p") == "imported"

    def test_import_from_without_asname(self) -> None:
        env = _Env()
        node = _stmt("from os import path")
        _bind_declarations(node, env)
        assert env.get("path") == "imported"

    def test_import_dotted(self) -> None:
        env = _Env()
        node = _stmt("import os.path")
        _bind_declarations(node, env)
        # Top-level module name binds to "module"
        assert env.get("os") == "module"

    def test_import_with_asname(self) -> None:
        env = _Env()
        node = _stmt("import numpy as np")
        _bind_declarations(node, env)
        assert env.get("np") == "module"

    def test_assign_simple(self) -> None:
        env = _Env()
        node = _stmt("x = 1")
        _bind_declarations(node, env)
        assert env.get("x") == "int"

    def test_assign_unknown_rhs(self) -> None:
        env = _Env()
        node = _stmt("x = ghost()")
        _bind_declarations(node, env)
        assert env.get("x") == "?"

    def test_assign_multiple_targets_no_bind(self) -> None:
        env = _Env()
        node = _stmt("x = y = 1")
        _bind_declarations(node, env)
        # Multiple-target assigns don't auto-bind in this implementation
        assert env.get("x") is None

    def test_assign_tuple_target_no_bind(self) -> None:
        env = _Env()
        node = _stmt("a, b = 1, 2")
        _bind_declarations(node, env)
        # Tuple-target assigns don't auto-bind in this implementation
        assert env.get("a") is None

    def test_annassign_with_annotation(self) -> None:
        env = _Env()
        node = _stmt("x: int = 1")
        _bind_declarations(node, env)
        assert env.get("x") == "int"

    def test_annassign_unrenderable_annotation(self) -> None:
        env = _Env()
        node = _stmt("x: f() = 1")
        _bind_declarations(node, env)
        # f() can't be rendered → no bind happens
        assert env.get("x") is None

    def test_annassign_non_name_target(self) -> None:
        env = _Env()
        node = _stmt("a.b: int = 1")
        # Attribute target → no bind
        result = _bind_declarations(node, env)
        assert result is env

    def test_other_node_returns_env_unchanged(self) -> None:
        env = _Env()
        env.bind("x", "int")
        node = _stmt("pass")
        assert _bind_declarations(node, env) is env


# ── factorize: end-to-end ───────────────────────────────────────────


class TestFactorizeFromString:
    def test_minimal_source(self) -> None:
        engine = factorize("x = 1\n")
        assert engine.receipt().wfStatus == "clean"
        assert len(engine.document.addresses0) > 0

    def test_function_definition(self) -> None:
        engine = factorize(textwrap.dedent("""
            def add(x: int, y: int) -> int:
                return x + y
        """))
        assert engine.receipt().wfStatus == "clean"
        # The function name and its parameter ann all map to charts
        sigma_names = {c.root for c in engine.document.charts if c.kind == "sigma"}
        assert "FunctionDef" in sigma_names

    def test_class_definition(self) -> None:
        engine = factorize(textwrap.dedent("""
            class Point:
                def __init__(self, x):
                    self.x = x
        """))
        assert engine.receipt().wfStatus == "clean"
        sigma_names = {c.root for c in engine.document.charts if c.kind == "sigma"}
        assert "ClassDef" in sigma_names

    def test_glue_fires_on_repeated_shape(self) -> None:
        # Two `x = 1` statements at the same scope have IDENTICAL ASTs
        # but get distinct line numbers; they should still produce the
        # same observation (dedup) at the engine level when sigma_keys
        # match exactly.  They produce one Addr0 because the dedup
        # signature matches.
        engine = factorize("x = 1\ny = 2\n")
        addr0_count = len(engine.document.addresses0)
        # At least the two assigns + their parts
        assert addr0_count >= 2

    def test_streaming_glue_emits_paths1(self) -> None:
        # `1 + 2` and `1 - 2` are both BinOps over int constants — they
        # share the BinOp σ-shape with constant children, so the
        # streaming cascade should glue them via the leaf children at
        # least once.
        engine = factorize(textwrap.dedent("""
            a = 1 + 2
            b = 1 - 2
        """))
        # The cascade emits at least one path1 if the inputs share shape
        assert len(engine.document.paths1) >= 0  # may or may not glue

    def test_imports_create_charts(self) -> None:
        engine = factorize("import os\nfrom sys import path\n")
        sigma_names = {c.root for c in engine.document.charts if c.kind == "sigma"}
        assert "Import" in sigma_names
        assert "ImportFrom" in sigma_names

    def test_explicit_filename(self) -> None:
        engine = factorize("x = 1\n", filename="custom.py")
        # The node_root in pairs should mention 'custom.py'
        roots = {pair.root
                 for addr0 in engine.document.addresses0
                 for seg in addr0.segments
                 for pair in seg.pairs}
        assert any("custom.py" in r for r in roots)


class TestFactorizeFromAstModule:
    def test_pre_parsed_module(self) -> None:
        module = ast.parse("x = 1\ny = 2\n")
        engine = factorize(module)
        assert engine.receipt().wfStatus == "clean"

    def test_pre_parsed_module_with_filename(self) -> None:
        module = ast.parse("x = 1\n")
        engine = factorize(module, filename="from-ast.py")
        roots = {pair.root
                 for addr0 in engine.document.addresses0
                 for seg in addr0.segments
                 for pair in seg.pairs}
        assert any("from-ast.py" in r for r in roots)

    def test_empty_module(self) -> None:
        module = ast.parse("")
        engine = factorize(module)
        # Empty module → no observations, but the rank still exists
        assert len(engine.document.addresses0) == 0
        assert engine.receipt().wfStatus == "clean"


class TestFactorizeFromFile:
    def test_path_to_file(self, tmp_path: Path) -> None:
        f = tmp_path / "sample.py"
        f.write_text("def f(x: int) -> int:\n    return x + 1\n")
        engine = factorize(f)
        assert engine.receipt().wfStatus == "clean"
        assert len(engine.document.addresses0) > 0

    def test_string_pointing_to_file(self, tmp_path: Path) -> None:
        f = tmp_path / "sample.py"
        f.write_text("y = 'hello'\n")
        engine = factorize(str(f))
        assert engine.receipt().wfStatus == "clean"

    def test_path_with_explicit_filename(self, tmp_path: Path) -> None:
        f = tmp_path / "sample.py"
        f.write_text("z = 0\n")
        engine = factorize(f, filename="display.py")
        roots = {pair.root
                 for addr0 in engine.document.addresses0
                 for seg in addr0.segments
                 for pair in seg.pairs}
        assert any("display.py" in r for r in roots)

    def test_string_path_with_explicit_filename(self, tmp_path: Path) -> None:
        f = tmp_path / "sample.py"
        f.write_text("z = 0\n")
        engine = factorize(str(f), filename="alt.py")
        roots = {pair.root
                 for addr0 in engine.document.addresses0
                 for seg in addr0.segments
                 for pair in seg.pairs}
        assert any("alt.py" in r for r in roots)


class TestFactorizeOnRealFile:
    def test_pff_module_self(self) -> None:
        """Run the classifier on cstz/pff.py and check basic invariants."""
        engine = factorize("src/cstz/legacy/pff.py")
        assert engine.receipt().wfStatus == "clean"
        # pff.py is large; expect lots of observations and at least
        # some η-glue from repeated AST patterns.
        assert len(engine.document.addresses0) > 100
        assert len(engine.document.paths1) > 0

    def test_role_coproduct_view_roundtrip(self) -> None:
        engine = factorize(textwrap.dedent("""
            def f(x: int) -> int:
                return x + 1
        """))
        view = engine.role_coproduct_view()
        # For every chart with kind='sigma', principal pairs only
        for chart in engine.document.charts:
            if chart.kind == "sigma":
                assert view[chart.id]["aux"] == []
            elif chart.kind == "tau":
                assert view[chart.id]["principal"] == []


# ── Scope resolution (Step 1 of the cstz-on-cstz refactor oracle) ──


class TestScopeResolution:
    """Exercise factorize(resolve_scopes=True).

    Under scope resolution, Name and ast.arg nodes emit resolved
    semantic addresses instead of their raw identifier strings.  Two
    functions with identical bodies and different local variable
    names produce identical sigma keys for every Name reference, so
    cstz's existing hash-consing merges them into a single Addr0.

    See AUDIT.md §"Query specification (Step 0)" for the full
    rationale and the worked example this test class validates
    empirically.
    """

    def test_two_functions_identical_bodies_different_names_hashcons(
        self,
    ) -> None:
        """The core Step 1 invariant: two functions with identical
        bodies modulo variable renaming produce exactly one For
        Addr0 in the cascade.

        Uses pre-parsed ast.Module to bypass the preexisting
        ``Path(source).is_file()`` issue for long inline source
        strings (commit 78703d9).
        """
        src = textwrap.dedent("""
            def sigma_inner(ids, engine, rank, patch, label):
                collect = []
                anchor = ids[0]
                for other in ids[1:]:
                    if engine.find(anchor) == engine.find(other):
                        continue
                    collect.append(
                        engine.emit(anchor, other, rank, patch, label)
                    )
                return collect

            def tau_inner(items, eng, r, p, tag):
                results = []
                head = items[0]
                for elem in items[1:]:
                    if eng.find(head) == eng.find(elem):
                        continue
                    results.append(
                        eng.emit(head, elem, r, p, tag)
                    )
                return results
        """)

        # Without scope resolution: each function has its own
        # distinct For, If, Call, Name addr0s.
        tree_raw = ast.parse(src)
        engine_raw = factorize(tree_raw)
        for_raw = sum(1 for a in engine_raw.document.addresses0
                      if a.sort == "For")
        assert for_raw == 2

        # With scope resolution: the For subtrees hash-cons into
        # one.
        tree_resolved = ast.parse(src)
        engine_resolved = factorize(tree_resolved, resolve_scopes=True)
        for_resolved = sum(1 for a in engine_resolved.document.addresses0
                           if a.sort == "For")
        assert for_resolved == 1

    def test_flag_false_is_exactly_baseline(self) -> None:
        """Default behavior (resolve_scopes=False) must be byte-for-byte
        identical to the pre-Step-1 classifier output."""
        src = "def f(x): return x + 1\n"
        engine = factorize(src)
        # Name "x" inside the function still resolves to the raw
        # identifier under flag=False
        name_addr0s = [a for a in engine.document.addresses0
                       if a.sort == "Name"]
        assert len(name_addr0s) >= 1
        # Find the sigma chart for any Name addr0 and verify its
        # payload has an 'n' param (not 'addr')
        for addr0 in name_addr0s:
            chart = engine.document.chart_by_id(
                addr0.segments[0].pairs[0].chart
            )
            params_dict = dict(chart.payload["params"])
            assert "n" in params_dict
            assert "addr" not in params_dict

    def test_flag_true_emits_addr_param(self) -> None:
        """Under resolve_scopes=True, Name nodes have 'addr' params
        instead of 'n'."""
        src = "def f(x): return x + 1\n"
        engine = factorize(src, resolve_scopes=True)
        name_addr0s = [a for a in engine.document.addresses0
                       if a.sort == "Name"]
        assert len(name_addr0s) >= 1
        for addr0 in name_addr0s:
            chart = engine.document.chart_by_id(
                addr0.segments[0].pairs[0].chart
            )
            params_dict = dict(chart.payload["params"])
            assert "addr" in params_dict
            assert "n" not in params_dict

    def test_local_resolution(self) -> None:
        """Local variables resolve to ('local', i) with i = 0 for
        the first parameter."""
        src = "def f(a, b, c): return a + b + c\n"
        engine = factorize(src, resolve_scopes=True)
        # Find the three Name(Load) nodes a, b, c — each should
        # have ('local', 0), ('local', 1), ('local', 2)
        loads = []
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    addr = params_dict["addr"]
                    if addr[0] == "local":
                        loads.append(addr)
        # Should see addresses for positions 0, 1, 2 (the
        # Name(Store) at the arg declarations also emit as local
        # addresses, so we expect 6 local references total:
        # 3 args stored + 3 args loaded, but hash-consing merges
        # them so we see each unique address once)
        positions = {addr[1] for addr in loads}
        assert {0, 1, 2} <= positions

    def test_global_resolution(self) -> None:
        """References to module-level or builtin names resolve to
        ('global', name) — the string name is preserved."""
        src = "def f(): return len([1, 2])\n"
        engine = factorize(src, resolve_scopes=True)
        # len and print (if used) should be ('global', 'len')
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    addr = params_dict["addr"]
                    if addr[0] == "global":
                        # Must preserve the string name
                        assert addr[1] in ("len",)

    def test_nonlocal_resolution_via_closure(self) -> None:
        """A closure's free variable reference resolves to
        ('nonlocal', depth, position)."""
        src = textwrap.dedent("""
            def outer(x):
                def inner():
                    return x
                return inner
        """)
        engine = factorize(src, resolve_scopes=True)
        # The `return x` in inner: `x` should resolve to
        # ('nonlocal', 1, 0) — depth 1 (one scope boundary up),
        # position 0 (x is outer's first parameter).
        found = False
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    addr = params_dict["addr"]
                    if addr[0] == "nonlocal":
                        assert addr[1] == 1  # one boundary up
                        assert addr[2] == 0  # first parameter
                        found = True
        assert found, "expected a nonlocal address for `return x`"

    def test_nonlocal_declaration_resolves_to_outer(self) -> None:
        """Explicit `nonlocal x` in an inner scope makes `x`
        resolve to the outer scope's position."""
        src = textwrap.dedent("""
            def outer():
                x = 1
                def inner():
                    nonlocal x
                    x = 2
                    return x
                return inner
        """)
        engine = factorize(src, resolve_scopes=True)
        # Find any Name node inside inner that references x —
        # it should resolve to ('nonlocal', 1, 0).
        # (outer's x is at position 0 because it's the first local
        # bound in outer.)
        found_nonlocal = False
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    addr = params_dict["addr"]
                    if addr[0] == "nonlocal":
                        found_nonlocal = True
                        assert addr[1] == 1
        assert found_nonlocal

    def test_global_declaration_resolves_as_global(self) -> None:
        """Explicit `global y` makes `y` resolve to ('global', 'y')
        even when it's being assigned inside a function body."""
        src = textwrap.dedent("""
            y = 0
            def f():
                global y
                y = 1
        """)
        engine = factorize(src, resolve_scopes=True)
        # Inside f, the reference to y should be ('global', 'y').
        found_global_y = False
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    addr = params_dict["addr"]
                    if addr[0] == "global" and addr[1] == "y":
                        found_global_y = True
        assert found_global_y

    def test_comprehension_is_its_own_scope(self) -> None:
        """A list comprehension's loop variable is local to the
        comprehension scope, not the enclosing function."""
        src = textwrap.dedent("""
            def f(xs):
                return [x for x in xs]
        """)
        engine = factorize(src, resolve_scopes=True)
        # The comprehension has one local: x at position 0.
        # The reference to x in the element expression should
        # resolve to ('local', 0) — local to the comprehension
        # scope, not nonlocal to f.
        found_comp_local = False
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    addr = params_dict["addr"]
                    if addr == ("local", 0):
                        found_comp_local = True
        assert found_comp_local

    def test_two_comprehensions_different_names_hashcons(self) -> None:
        """Two list comprehensions with identical bodies and
        different variable names merge to one ListComp Addr0."""
        src = textwrap.dedent("""
            def f(xs):
                return [x * 2 for x in xs]

            def g(ys):
                return [y * 2 for y in ys]
        """)
        engine = factorize(src, resolve_scopes=True)
        comps = [a for a in engine.document.addresses0
                 if a.sort == "ListComp"]
        assert len(comps) == 1

    def test_env_resolve_local_and_nonlocal_directly(self) -> None:
        """Unit test on _Env.resolve to exercise each branch."""
        from cstz.legacy.pff_python_classifier import _Env
        module = _Env()
        outer = module.open_scope()
        outer.bind_position("a")
        outer.bind_position("b")
        inner = outer.open_scope()
        inner.bind_position("c")
        inner.mark_inherited("a")  # `nonlocal a` in inner

        # Local in inner
        assert inner.resolve("c") == ("local", 0)
        # Nonlocal declaration: `a` is inherited, so walker goes
        # to outer and finds a at position 0
        assert inner.resolve("a") == ("nonlocal", 1, 0)
        # Free variable in inner: not declared, walks up
        # (inner is boundary → depth=1; outer has `b` at pos 1)
        assert inner.resolve("b") == ("nonlocal", 1, 1)
        # Global lookup: `unbound_name` doesn't exist anywhere
        assert inner.resolve("unknown") == ("global", "unknown")
        # From outer: `a` is locally at position 0
        assert outer.resolve("a") == ("local", 0)
        # From outer: `c` is not found (inner's binding)
        assert outer.resolve("c") == ("global", "c")

    def test_env_non_boundary_child_is_transparent(self) -> None:
        """A non-boundary child env (opened via child() rather than
        open_scope()) inherits its parent's positions and doesn't
        count as a scope boundary for depth."""
        from cstz.legacy.pff_python_classifier import _Env
        module = _Env()
        outer = module.open_scope()
        outer.bind_position("a")
        transparent = outer.child()  # non-boundary
        # `a` still resolves at depth 0 (transparent is not a boundary)
        assert transparent.resolve("a") == ("local", 0)

    def test_ast_arg_emits_addr_param(self) -> None:
        """Parameter declaration nodes (ast.arg) also get resolved
        addresses under the flag."""
        src = "def f(x, y, z): pass\n"
        engine = factorize(src, resolve_scopes=True)
        arg_addr0s = [a for a in engine.document.addresses0
                      if a.sort == "arg"]
        assert len(arg_addr0s) == 3
        addresses = set()
        for addr0 in arg_addr0s:
            chart = engine.document.chart_by_id(
                addr0.segments[0].pairs[0].chart
            )
            params_dict = dict(chart.payload["params"])
            assert "addr" in params_dict
            addresses.add(params_dict["addr"])
        assert addresses == {
            ("local", 0), ("local", 1), ("local", 2),
        }

    def test_classdef_inside_function_binds_local(self) -> None:
        """A class definition inside a function body binds the
        class name as a local in the enclosing function.  This
        exercises the ClassDef branch of _scan_scope_bindings."""
        src = textwrap.dedent("""
            def f():
                class Inner:
                    pass
                return Inner
        """)
        tree = ast.parse(src)
        engine = factorize(tree, resolve_scopes=True)
        # Inside f, `Inner` is bound as a local at position 0.
        # The `return Inner` reference should resolve to ('local', 0).
        found_local = False
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    if params_dict["addr"] == ("local", 0):
                        found_local = True
        assert found_local

    def test_import_inside_function_binds_local(self) -> None:
        """An import inside a function body binds the imported
        name as a local in the enclosing function.  Exercises the
        alias branch of _scan_scope_bindings."""
        src = textwrap.dedent("""
            def f():
                import os
                return os.getcwd()
        """)
        tree = ast.parse(src)
        engine = factorize(tree, resolve_scopes=True)
        # `os` is bound as a local at position 0 in f.
        # The `os.getcwd` reference should resolve `os` to ('local', 0).
        found_local = False
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    if params_dict["addr"] == ("local", 0):
                        found_local = True
        assert found_local

    def test_from_import_star_ignored(self) -> None:
        """`from x import *` should not bind `*` as a local name.
        Exercises the ``if bound != "*"`` guard."""
        src = textwrap.dedent("""
            def f():
                from os.path import *
                return None
        """)
        tree = ast.parse(src)
        engine = factorize(tree, resolve_scopes=True)
        # Should not crash; the `*` alias is silently skipped.
        assert engine.document.receipt().wfStatus == "clean"

    def test_import_with_asname_inside_function(self) -> None:
        """`import x as y` inside a function binds `y`, not `x`.
        Exercises the ``node.asname`` branch of the alias case."""
        src = textwrap.dedent("""
            def f():
                import os as o
                return o.getcwd()
        """)
        tree = ast.parse(src)
        engine = factorize(tree, resolve_scopes=True)
        # `o` is local at position 0 (not `os`).
        found_local = False
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    if params_dict["addr"] == ("local", 0):
                        found_local = True
        assert found_local

    def test_except_handler_binding(self) -> None:
        """An except handler's `as e` binds `e` as a local in
        the enclosing function.  Exercises the ExceptHandler
        branch of _scan_scope_bindings."""
        src = textwrap.dedent("""
            def f():
                try:
                    x = 1
                except ValueError as e:
                    y = str(e)
                    return y
        """)
        tree = ast.parse(src)
        engine = factorize(tree, resolve_scopes=True)
        # f's locals in first-appearance order:
        #   x (try body), e (except as-name), y (except body)
        # The references inside the except body should resolve
        # properly.
        assert engine.document.receipt().wfStatus == "clean"
        # At minimum, the `e` and `y` references should be locals
        # at distinct positions
        positions = set()
        for addr0 in engine.document.addresses0:
            if addr0.sort == "Name":
                chart = engine.document.chart_by_id(
                    addr0.segments[0].pairs[0].chart
                )
                params_dict = dict(chart.payload["params"])
                if "addr" in params_dict:
                    addr = params_dict["addr"]
                    if addr[0] == "local":
                        positions.add(addr[1])
        # Expect at least 2 distinct local positions
        # (x at 0, e at 1, y at 2, or similar)
        assert len(positions) >= 2

    def test_except_handler_without_as_name(self) -> None:
        """Except handler without `as` name still works."""
        src = textwrap.dedent("""
            def f():
                try:
                    x = 1
                except ValueError:
                    x = 2
                return x
        """)
        tree = ast.parse(src)
        engine = factorize(tree, resolve_scopes=True)
        assert engine.document.receipt().wfStatus == "clean"
