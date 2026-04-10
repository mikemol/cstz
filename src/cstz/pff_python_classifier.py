"""Python AST → PFF cascade.

Parallel implementation of cstz.python_classifier in PFF vocabulary.
Walks a Python AST and emits one observation per node into a
PFFCascadeEngine, returning the engine for inspection.

This module deliberately omits the static type-inference tables
(_KNOWN_TYPES, _RECV_ATTR, _METHOD_RET, _PARAM_TYPES) that
python_classifier.py uses.  Project-specific type knowledge —
rdflib, pathlib, ast — is not baked in here.  The type environment
is built dynamically from the source: imports, class definitions,
function definitions, parameter annotations, and assignments
contribute bindings.  The only baked-in vocabulary is Python's own
language builtins (`int`, `str`, `len`, `print`, …), and even those
are seeded as plain `builtin`/`type` markers rather than as rich
type signatures.

The legacy ``cstz.python_classifier`` and its tests remain the
metamathematical reference for inference.agda.  This module is a
parallel implementation in PFF vocabulary; it does not import from
``core``, ``python_classifier``, or ``agda_synth``.

Usage::

    from cstz.pff_python_classifier import factorize

    engine = factorize("path/to/source.py")
    print(engine)
    print(engine.receipt().wfStatus)
"""

from __future__ import annotations

import ast
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union

from .pff_cascade import PFFCascadeEngine


# ── Python language vocabulary (the only baked-in knowledge) ────────


# Map literal Python value type → τ-chart root.  Covers every
# `ast.Constant` payload type that Python emits at parse time.
_LITERAL_TYPE_NAMES: Dict[type, str] = {
    type(None): "NoneType",
    bool: "bool",
    int: "int",
    float: "float",
    complex: "complex",
    str: "str",
    bytes: "bytes",
}


# Builtin callables.  Bound in every root environment so that
# `len(...)`, `print(...)`, etc. resolve to a meaningful τ.  Each
# value is the τ-chart root for the *return type*; the special
# value "type" means the name is itself a constructor whose call
# returns an instance of that type (e.g. `int(x)` → "int").
_BUILTIN_CALLABLES: Dict[str, str] = {
    "len": "int",
    "abs": "int",
    "min": "?",
    "max": "?",
    "sum": "?",
    "any": "bool",
    "all": "bool",
    "isinstance": "bool",
    "issubclass": "bool",
    "hasattr": "bool",
    "getattr": "?",
    "setattr": "NoneType",
    "repr": "str",
    "str": "type",
    "int": "type",
    "float": "type",
    "bool": "type",
    "bytes": "type",
    "list": "type",
    "dict": "type",
    "set": "type",
    "tuple": "type",
    "frozenset": "type",
    "type": "type",
    "object": "type",
    "range": "range",
    "enumerate": "enumerate",
    "zip": "zip",
    "iter": "iter",
    "next": "?",
    "id": "int",
    "hash": "int",
    "sorted": "list",
    "reversed": "iter",
    "open": "file",
    "print": "NoneType",
}

# Builtin singletons.
_BUILTIN_SINGLETONS: Dict[str, str] = {
    "True": "bool",
    "False": "bool",
    "None": "NoneType",
    "Ellipsis": "ellipsis",
    "__name__": "str",
    "__file__": "str",
}


# ── Type environment ────────────────────────────────────────────────


class _Env:
    """Lexical type environment built dynamically from source.

    Bindings come exclusively from:
      - Python language builtins (seeded by ``_seeded_root_env``)
      - Class / function / import declarations encountered while walking
      - Assignments whose RHS type is inferable

    No project-specific tables are baked in.  An identifier with no
    binding resolves to ``None`` and the τ-chart root falls back to
    ``"?"``.
    """

    __slots__ = ("_bindings", "_parent")

    def __init__(self, parent: Optional["_Env"] = None) -> None:
        self._bindings: Dict[str, str] = {}
        self._parent: Optional[_Env] = parent

    def bind(self, name: str, typ: str) -> None:
        self._bindings[name] = typ

    def get(self, name: str) -> Optional[str]:
        if name in self._bindings:
            return self._bindings[name]
        if self._parent is not None:
            return self._parent.get(name)
        return None

    def child(self) -> "_Env":
        return _Env(self)


def _seeded_root_env() -> _Env:
    """Build a root environment seeded with Python language builtins."""
    env = _Env()
    for name, ret_or_kind in _BUILTIN_CALLABLES.items():
        # We tag callables with `→<ret>` so the inference for `Call`
        # nodes can recognize them as arrows; constructors are tagged
        # `type` so calls produce a value of that type.
        if ret_or_kind == "type":
            env.bind(name, "type")
        else:
            env.bind(name, f"→{ret_or_kind}")
    for name, typ in _BUILTIN_SINGLETONS.items():
        env.bind(name, typ)
    return env


# ── τ-inference (no project tables) ─────────────────────────────────


def _annotation_to_str(node: Optional[ast.expr]) -> Optional[str]:
    """Render a Python type annotation to its τ-chart root form.

    Handles the common shapes: ``Name``, string forward refs,
    ``Attribute`` (qualified names), and ``Subscript`` (generic
    instantiations — we record the outer constructor only).
    """
    if node is None:
        return None
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.Attribute):
        base = _annotation_to_str(node.value)
        return f"{base}.{node.attr}" if base else node.attr
    if isinstance(node, ast.Subscript):
        return _annotation_to_str(node.value)
    return None


def _infer_type(node: ast.AST, env: _Env) -> str:
    """Infer the τ-chart root for an AST node within an environment.

    Returns "?" for nodes whose type cannot be inferred from
    Python-language semantics + the dynamic environment.
    """
    if isinstance(node, ast.Constant):
        return _LITERAL_TYPE_NAMES.get(type(node.value), "?")
    if isinstance(node, ast.Name):
        bound = env.get(node.id)
        return bound if bound is not None else "?"
    if isinstance(node, ast.JoinedStr):
        return "str"
    if isinstance(node, ast.FormattedValue):
        return "str"
    if isinstance(node, ast.List):
        return "list"
    if isinstance(node, ast.Dict):
        return "dict"
    if isinstance(node, ast.Set):
        return "set"
    if isinstance(node, ast.Tuple):
        return "tuple"
    if isinstance(node, ast.ListComp):
        return "list"
    if isinstance(node, ast.SetComp):
        return "set"
    if isinstance(node, ast.DictComp):
        return "dict"
    if isinstance(node, ast.GeneratorExp):
        return "iter"
    if isinstance(node, ast.Lambda):
        return "callable"
    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name):
            bound = env.get(node.func.id)
            if bound is not None:
                if bound.startswith("→"):
                    return bound[1:]
                if bound == "type":
                    return node.func.id
        return "?"
    if isinstance(node, ast.Attribute):
        # We do not bake in receiver→attr tables.  Without per-class
        # field knowledge the best we can do is record the qualified
        # access form so two identical accesses share a τ-chart.
        base = _infer_type(node.value, env)
        return f"{base}.{node.attr}" if base != "?" else "?"
    return "?"


# ── κ-classification (intrinsic categorical roles only) ─────────────


def _classify_kappa(node: ast.AST) -> str:
    """Classify an AST node by its intrinsic categorical role.

    No project-specific patterns: only language-intrinsic universal
    construction tags.  Compare with python_classifier._classify_kappa
    which baked in domain-qualified tags like ``graph.emit``.
    """
    if isinstance(node, ast.Constant):
        return "terminal"
    if isinstance(node, ast.Name):
        return "bind" if isinstance(node.ctx, ast.Store) else "var"
    if isinstance(node, ast.Attribute):
        return "morphism"
    if isinstance(node, ast.Call):
        return "apply"
    if isinstance(node, ast.Assign):
        return "let"
    if isinstance(node, ast.AnnAssign):
        return "let"
    if isinstance(node, ast.AugAssign):
        return "monoid.accum"
    if isinstance(node, ast.For):
        return "fold"
    if isinstance(node, ast.AsyncFor):
        return "fold"
    if isinstance(node, ast.While):
        return "fixpoint"
    if isinstance(node, ast.If):
        return "coproduct.elim"
    if isinstance(node, ast.IfExp):
        return "coproduct.elim"
    if isinstance(node, ast.Return):
        return "terminal.map"
    if isinstance(node, ast.Tuple):
        return "product.unpack" if isinstance(node.ctx, ast.Store) else "product"
    if isinstance(node, ast.List):
        return "free_monoid.literal"
    if isinstance(node, ast.Dict):
        return "exponential.literal"
    if isinstance(node, ast.Set):
        return "powerset.literal"
    if isinstance(node, ast.ListComp):
        return "free_monoid.map"
    if isinstance(node, ast.SetComp):
        return "powerset.map"
    if isinstance(node, ast.DictComp):
        return "exponential.map"
    if isinstance(node, ast.GeneratorExp):
        return "lazy_fold"
    if isinstance(node, ast.BoolOp):
        return "meet" if isinstance(node.op, ast.And) else "join"
    if isinstance(node, ast.Compare):
        return "equalizer"
    if isinstance(node, ast.BinOp):
        return "binop"
    if isinstance(node, ast.UnaryOp):
        return "complement" if isinstance(node.op, ast.Not) else "endomorphism"
    if isinstance(node, ast.JoinedStr):
        return "free_monoid.fold"
    if isinstance(node, ast.FormattedValue):
        return "coerce"
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        return "exponential.intro"
    if isinstance(node, ast.ClassDef):
        return "classifier.intro"
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return "pullback.import"
    if isinstance(node, ast.Expr):
        return "effect.seq"
    if isinstance(node, ast.Raise):
        return "initial"
    if isinstance(node, ast.Try):
        return "coproduct.handle"
    if isinstance(node, ast.With):
        return "monad.bind"
    if isinstance(node, ast.AsyncWith):
        return "monad.bind"
    if isinstance(node, ast.Yield):
        return "cofree"
    if isinstance(node, ast.YieldFrom):
        return "cofree"
    if isinstance(node, ast.Await):
        return "monad.bind"
    if isinstance(node, ast.Pass):
        return "identity"
    if isinstance(node, ast.Break):
        return "fixpoint.halt"
    if isinstance(node, ast.Continue):
        return "fixpoint.next"
    if isinstance(node, ast.Global):
        return "scope.escape"
    if isinstance(node, ast.Nonlocal):
        return "scope.escape"
    if isinstance(node, ast.Delete):
        return "annihilate"
    if isinstance(node, ast.Starred):
        return "spread"
    if isinstance(node, ast.Subscript):
        return "index"
    if isinstance(node, ast.Slice):
        return "slice"
    return type(node).__name__.lower()


# ── Param extraction (identity-discriminating syntactic data) ───────


def _extract_params(node: ast.AST) -> Tuple[Tuple[str, Any], ...]:
    """Pull the syntactic params that distinguish nodes of the same kind.

    Two ``Name("foo")`` nodes have the same identity-class; two
    ``Name("bar")`` nodes have the same identity-class; the two
    classes are distinct.  This is what makes the σ-chart partition
    interesting in the cascade — without these params every Name node
    would collapse to a single chart.
    """
    params: Dict[str, Any] = {}
    if isinstance(node, ast.Name):
        params["n"] = node.id
    elif isinstance(node, ast.Attribute):
        params["a"] = node.attr
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        params["n"] = node.name
    elif isinstance(node, ast.Constant):
        v = repr(node.value)
        params["v"] = v if len(v) <= 80 else f"<long:{len(v)}>"
    elif isinstance(node, ast.arg):
        params["n"] = node.arg
    elif isinstance(node, ast.alias):
        params["n"] = node.name
        if node.asname:
            params["as"] = node.asname
    elif isinstance(node, ast.ImportFrom):
        params["m"] = node.module or ""
    elif isinstance(node, ast.Import):
        params["m"] = ",".join(a.name for a in (node.names or []))
    elif isinstance(node, ast.keyword):
        if node.arg is not None:
            params["n"] = node.arg
    elif isinstance(node, (ast.Global, ast.Nonlocal)):
        params["n"] = ",".join(node.names)
    return tuple(sorted(params.items()))


# ── Walker ──────────────────────────────────────────────────────────


def _bind_declarations(node: ast.AST, env: _Env) -> _Env:
    """Update *env* with bindings introduced by *node* (in the outer
    scope) and return the environment to use for *node*'s children.

    For most nodes the children share *env*; for scope-introducing
    nodes (FunctionDef, ClassDef, Lambda) we open a fresh child env
    and seed it with parameter bindings.
    """
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        ret_ann = _annotation_to_str(node.returns)
        env.bind(node.name, f"→{ret_ann}" if ret_ann else "→?")
        child = env.child()
        for arg in node.args.args:
            ann = _annotation_to_str(arg.annotation)
            child.bind(arg.arg, ann or "?")
        return child
    if isinstance(node, ast.ClassDef):
        env.bind(node.name, "type")
        return env.child()
    if isinstance(node, ast.Lambda):
        child = env.child()
        for arg in node.args.args:
            child.bind(arg.arg, "?")
        return child
    if isinstance(node, ast.ImportFrom):
        for alias in (node.names or []):
            nm = alias.asname or alias.name
            env.bind(nm, "imported")
        return env
    if isinstance(node, ast.Import):
        for alias in (node.names or []):
            nm = alias.asname or alias.name.split(".")[0]
            env.bind(nm, "module")
        return env
    if isinstance(node, ast.Assign):
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            env.bind(node.targets[0].id, _infer_type(node.value, env))
        return env
    if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
        ann = _annotation_to_str(node.annotation)
        if ann is not None:
            env.bind(node.target.id, ann)
        return env
    return env


def _walk(
    node: ast.AST,
    engine: PFFCascadeEngine,
    env: _Env,
    filename: str,
    rank: Any,
    patch: Any,
) -> str:
    """Recursively factorize an AST node into engine observations.

    Returns the addr0 id of the new observation.
    """
    ast_type = type(node).__name__
    params = _extract_params(node)

    # Bind declarations introduced by this node and select the
    # environment to use for the children.
    child_env = _bind_declarations(node, env)

    # Walk children left-to-right.
    child_addr0_ids: List[str] = []
    for child in ast.iter_child_nodes(node):
        child_addr0_ids.append(
            _walk(child, engine, child_env, filename, rank, patch)
        )

    # Compute σ and τ charts.  σ is keyed by (ast_type, params,
    # kappa_tag) so two nodes with the same shape but different
    # categorical roles are kept distinct.
    kappa_tag = _classify_kappa(node)
    sigma_chart = engine.ensure_chart(
        kind="sigma",
        root=ast_type,
        payload={"params": list(params), "kappa": kappa_tag},
        patch=patch,
    )
    tau_root = _infer_type(node, env)
    tau_chart = engine.ensure_chart(
        kind="tau",
        root=tau_root,
        patch=patch,
    )

    addr0 = engine.add_observation(
        sigma_chart=sigma_chart,
        tau_chart=tau_chart,
        sigma_children=child_addr0_ids,
        sort=ast_type,
        node_root=f"{ast_type}@{filename}:{getattr(node, 'lineno', 0)}",
        rank=rank,
        patch=patch,
    )
    return addr0.id


# ── Public API ──────────────────────────────────────────────────────


def factorize(
    source: Union[str, Path, ast.Module],
    document_id: str = "cstz-pff-doc",
    filename: Optional[str] = None,
) -> PFFCascadeEngine:
    """Factorize Python source into a populated PFFCascadeEngine.

    ``source`` may be:
      - an ``ast.Module`` object (already-parsed)
      - a ``Path`` or ``str`` pointing at an existing ``.py`` file
      - any other ``str`` is parsed as inline source text

    Returns the engine.  ``engine.document`` is the PFF Document.
    ``engine.receipt().wfStatus`` is ``"clean"`` by construction.
    """
    engine = PFFCascadeEngine(document_id=document_id)
    rank = engine.ensure_rank(0, label="ast-ingest")
    patch = engine.ensure_patch("ingest", rank=rank)

    if isinstance(source, ast.Module):
        env = _seeded_root_env()
        display = filename or "<input>"
        for stmt in source.body:
            _walk(stmt, engine, env, display, rank, patch)
        return engine

    if isinstance(source, Path):
        text = source.read_text()
        tree = ast.parse(text)
        env = _seeded_root_env().child()
        display = filename or source.stem
        for stmt in tree.body:
            _walk(stmt, engine, env, display, rank, patch)
        return engine

    # str: try as path first, fall back to inline source.
    candidate = Path(source)
    if candidate.is_file():
        text = candidate.read_text()
        tree = ast.parse(text)
        env = _seeded_root_env().child()
        display = filename or candidate.stem
        for stmt in tree.body:
            _walk(stmt, engine, env, display, rank, patch)
        return engine

    tree = ast.parse(source)
    env = _seeded_root_env()
    display = filename or "<input>"
    for stmt in tree.body:
        _walk(stmt, engine, env, display, rank, patch)
    return engine


__all__ = ["factorize"]
