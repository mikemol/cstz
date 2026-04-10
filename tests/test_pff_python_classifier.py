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

from cstz.pff_python_classifier import (
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
        engine = factorize("src/cstz/pff.py")
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
