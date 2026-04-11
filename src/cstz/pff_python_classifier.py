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
from typing import Any, Dict, List, Optional, Set, Tuple, Union

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

    Scope resolution (Step 1 of the cstz-on-cstz refactor oracle
    plan) uses two additional fields:

      - ``_positions`` — first-appearance position of each local
        name in this scope.  Populated when the scope is entered;
        used by ``resolve`` to emit canonical positional addresses
        for Name references.
      - ``_inherited`` — names declared ``global`` or ``nonlocal``
        in this scope.  Lookups for inherited names walk the
        parent chain instead of resolving locally, preserving
        Python's scoping semantics.
      - ``_is_scope_boundary`` — True for the module scope and for
        every function / lambda / comprehension scope.  False for
        "child envs" created for import or assign-style updates,
        which share their parent scope's positional addresses.
        Only scope-boundary envs participate in the nonlocal depth
        count.

    Scope resolution is opt-in (see ``resolve_scopes`` flag on
    ``factorize``).  When disabled, ``_positions`` stays empty and
    ``_inherited`` stays empty, and ``resolve`` is never called.
    """

    __slots__ = (
        "_bindings", "_parent",
        "_positions", "_inherited", "_is_scope_boundary",
    )

    def __init__(
        self,
        parent: Optional["_Env"] = None,
        is_scope_boundary: bool = False,
    ) -> None:
        self._bindings: Dict[str, str] = {}
        self._parent: Optional[_Env] = parent
        self._positions: Dict[str, int] = {}
        self._inherited: Set[str] = set()
        self._is_scope_boundary: bool = is_scope_boundary

    def bind(self, name: str, typ: str) -> None:
        self._bindings[name] = typ

    def get(self, name: str) -> Optional[str]:
        if name in self._bindings:
            return self._bindings[name]
        if self._parent is not None:
            return self._parent.get(name)
        return None

    def child(self) -> "_Env":
        # Non-boundary child env: inherits the parent's scope
        # identity, used for per-statement binding updates within a
        # single function body.
        return _Env(self, is_scope_boundary=False)

    def open_scope(self) -> "_Env":
        """Open a new lexical scope.

        Used at FunctionDef / AsyncFunctionDef / Lambda / comprehension
        boundaries.  The new scope has its own ``_positions`` and
        ``_inherited`` sets, distinct from the parent's.
        """
        return _Env(self, is_scope_boundary=True)

    # ── Scope resolution (Step 1) ────────────────────────────────

    def mark_inherited(self, name: str) -> None:
        """Mark ``name`` as declared global/nonlocal in this scope.

        Inherited names are NOT assigned a local position; their
        ``resolve`` calls walk the parent chain instead.
        """
        self._inherited.add(name)

    def bind_position(self, name: str) -> None:
        """Assign ``name`` the next available local position.

        Idempotent: if ``name`` is already positioned or marked
        inherited, this is a no-op.  The caller is responsible for
        populating ``_positions`` before any Name references to
        ``name`` are resolved — typically via a first-pass scan of
        the scope body in ``_bind_declarations``.
        """
        if name in self._inherited:
            return
        if name in self._positions:
            return
        self._positions[name] = len(self._positions)

    def resolve(self, name: str) -> Tuple[str, ...]:
        """Return the semantic address of a Name reference.

        The return shape is one of:

          - ``("local", i)`` — local at position ``i`` in the current
            scope
          - ``("nonlocal", depth, i)`` — local at position ``i`` in
            the scope ``depth`` boundary-frames up from this one
          - ``("global", name)`` — resolved to a top-level / module
            scope name (depth equals the number of boundary frames
            between here and the module)
          - ``("free", name)`` — not found in any scope frame on the
            way up; treated as a builtin or unresolved reference

        "Scope boundary" here means a FunctionDef / AsyncFunctionDef
        / Lambda / comprehension frame.  Non-boundary child envs
        (used for per-statement type-binding updates) are transparent
        to the walker: their positions belong to the nearest enclosing
        boundary.
        """
        # Find the nearest scope frame that binds ``name``.
        # Depth counts scope-boundary frames we walk PAST without
        # finding the name, so a local in the current scope has
        # depth 0, a local in the immediately-enclosing scope
        # (closure) has depth 1, and so on.
        #
        # Inherited names (declared global or nonlocal in the
        # current scope) are skipped in the local lookup — the
        # walker continues to the parent chain.  In that case we
        # ALSO bump depth if the current env is a boundary, because
        # we're walking past the boundary to reach the outer scope
        # where the declaration points.
        env: Optional[_Env] = self
        depth = 0
        while env is not None:
            skip_local = name in env._inherited
            if not skip_local and name in env._positions:
                if depth == 0:
                    return ("local", env._positions[name])
                return ("nonlocal", depth, env._positions[name])
            # Walking past this env — bump depth if it's a boundary
            if env._is_scope_boundary:
                depth += 1
            env = env._parent
        # Not found in any scope frame.  Treat as global / builtin.
        return ("global", name)


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


def _extract_params(
    node: ast.AST,
    env: Optional[_Env] = None,
    resolve_scopes: bool = False,
) -> Tuple[Tuple[str, Any], ...]:
    """Pull the syntactic params that distinguish nodes of the same kind.

    Two ``Name("foo")`` nodes have the same identity-class; two
    ``Name("bar")`` nodes have the same identity-class; the two
    classes are distinct.  This is what makes the σ-chart partition
    interesting in the cascade — without these params every Name node
    would collapse to a single chart.

    Scope-resolution mode (when ``resolve_scopes=True`` and ``env`` is
    not None): ``Name`` and ``ast.arg`` nodes emit a resolved
    semantic address instead of their raw identifier string.  Two
    functions with identical bodies but different local variable
    names then produce identical params for every Name reference,
    which lets cstz's existing hash-consing merge them into a single
    Addr0.  See the ``_Env.resolve`` docstring for the address shape
    and the plan file's Step 1 for the rationale.

    When ``resolve_scopes=False`` (default), behavior is identical
    to the pre-scope-resolution classifier: Name and arg nodes carry
    their raw identifier string as the ``n`` param.
    """
    params: Dict[str, Any] = {}
    if isinstance(node, ast.Name):
        if resolve_scopes and env is not None:
            params["addr"] = env.resolve(node.id)
        else:
            params["n"] = node.id
    elif isinstance(node, ast.Attribute):
        params["a"] = node.attr
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        params["n"] = node.name
    elif isinstance(node, ast.Constant):
        v = repr(node.value)
        params["v"] = v if len(v) <= 80 else f"<long:{len(v)}>"
    elif isinstance(node, ast.arg):
        if resolve_scopes and env is not None:
            params["addr"] = env.resolve(node.arg)
        else:
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


# ── Scope-boundary binding collection (Step 1 helpers) ─────────────
#
# These helpers populate a fresh scope's ``_positions`` and
# ``_inherited`` fields by scanning the scope body upfront, before
# the walker descends into its children.  Upfront population is
# necessary because a Name reference early in a function body can
# resolve to a local defined later in the same body — under lazy
# collection, the reference would resolve incorrectly.
#
# Two passes per scope body:
#   Pass 1: mark names declared ``global`` or ``nonlocal`` as
#           inherited (they resolve in an outer frame).
#   Pass 2: assign local positions to every binding target found.
#
# Neither pass descends into nested scopes; those scopes will be
# handled separately by the walker when it enters them.


def _scan_scope_modifiers(node: ast.AST, scope: _Env) -> None:
    """First pass: mark ``global`` / ``nonlocal`` declarations."""
    if isinstance(node, ast.Global):
        for name in node.names:
            scope.mark_inherited(name)
        return
    if isinstance(node, ast.Nonlocal):
        for name in node.names:
            scope.mark_inherited(name)
        return
    if isinstance(
        node,
        (
            ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
            ast.ClassDef,
            ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
        ),
    ):
        return  # nested scope; its declarations don't affect us
    for child in ast.iter_child_nodes(node):
        _scan_scope_modifiers(child, scope)


def _scan_scope_bindings(node: ast.AST, scope: _Env) -> None:
    """Second pass: populate ``_positions`` for every local name.

    Descends into control-flow statements (if/while/for/try/with)
    but stops at nested scope boundaries.  Inherited names (already
    marked by pass 1) are silently skipped by ``scope.bind_position``.
    """
    if isinstance(node, ast.Name):
        if isinstance(node.ctx, ast.Store):
            scope.bind_position(node.id)
        return
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        scope.bind_position(node.name)
        return  # do not descend
    if isinstance(node, ast.ClassDef):
        scope.bind_position(node.name)
        return  # class body is not a new scope, but its members
                # are attributes, not locals in the enclosing scope
    if isinstance(node, (ast.Lambda, ast.ListComp, ast.SetComp,
                         ast.DictComp, ast.GeneratorExp)):
        return  # nested scope
    if isinstance(node, (ast.Global, ast.Nonlocal)):
        return  # handled by pass 1
    # ast.arg is not reachable through this scanner because we
    # don't recurse into FunctionDef/Lambda bodies from here;
    # their params are bound separately in _populate_scope.
    if isinstance(node, ast.alias):
        bound = node.asname if node.asname else node.name.split(".")[0]
        if bound != "*":
            scope.bind_position(bound)
        return
    if isinstance(node, ast.ExceptHandler):
        if node.name is not None:
            scope.bind_position(node.name)
        for stmt in node.body:
            _scan_scope_bindings(stmt, scope)
        return
    # For every other node, recurse into children
    for child in ast.iter_child_nodes(node):
        _scan_scope_bindings(child, scope)


def _populate_scope(
    params: List[ast.arg],
    body: List[ast.AST],
    scope: _Env,
) -> None:
    """Populate a fresh function / lambda scope with parameter and
    body bindings.

    Parameters get the first positions (0, 1, 2, ...).  Then the
    body is scanned in two passes (modifiers then bindings) to fill
    in local variable positions.
    """
    for arg in params:
        scope.bind_position(arg.arg)
    for stmt in body:
        _scan_scope_modifiers(stmt, scope)
    for stmt in body:
        _scan_scope_bindings(stmt, scope)


def _populate_comprehension_scope(
    generators: List[ast.comprehension],
    scope: _Env,
) -> None:
    """Populate a fresh comprehension scope.

    Each generator's target is bound in the comprehension scope.
    The first generator's iter is evaluated in the enclosing
    scope, so its Name references resolve in the parent chain —
    the walker handles this by visiting the iter BEFORE pushing
    this scope.  Modifier scanning is not relevant for
    comprehensions (they can't contain global/nonlocal).
    """
    for gen in generators:
        _scan_scope_bindings(gen.target, scope)


# ── Walker ──────────────────────────────────────────────────────────


def _bind_declarations(node: ast.AST, env: _Env) -> _Env:
    """Update *env* with bindings introduced by *node* (in the outer
    scope) and return the environment to use for *node*'s children.

    For most nodes the children share *env*; for scope-introducing
    nodes (FunctionDef, ClassDef, Lambda) we open a fresh scope env
    and seed it with parameter bindings.

    Under scope resolution, FunctionDef / AsyncFunctionDef / Lambda
    also populate the new scope's ``_positions`` upfront via a
    two-pass scan of the body (see ``_populate_scope``), so that
    Name references early in the body can resolve to locals defined
    later in the body.
    """
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        ret_ann = _annotation_to_str(node.returns)
        env.bind(node.name, f"→{ret_ann}" if ret_ann else "→?")
        child = env.open_scope()
        _populate_scope(node.args.args, node.body, child)
        for arg in node.args.args:
            ann = _annotation_to_str(arg.annotation)
            child.bind(arg.arg, ann or "?")
        return child
    if isinstance(node, ast.ClassDef):
        env.bind(node.name, "type")
        return env.child()
    if isinstance(node, ast.Lambda):
        child = env.open_scope()
        _populate_scope(node.args.args, [], child)
        for arg in node.args.args:
            child.bind(arg.arg, "?")
        return child
    if isinstance(
        node,
        (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp),
    ):
        # Comprehensions are a new scope in Python 3.  The walker
        # visits all children with this scope, including the first
        # generator's iter.  In Python semantics the first iter is
        # technically evaluated in the enclosing scope, but for
        # resolve() that doesn't matter: the comprehension scope's
        # _positions only contains the generator targets, so any
        # free variable (like `xs` in `[x for x in xs]`) walks the
        # parent chain and resolves to the enclosing-scope name
        # with a nonlocal depth of 1 — which is semantically correct.
        child = env.open_scope()
        _populate_comprehension_scope(node.generators, child)
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
    resolve_scopes: bool = False,
) -> str:
    """Recursively factorize an AST node into engine observations.

    Returns the addr0 id of the new observation.

    ``resolve_scopes``: when True, Name and ast.arg nodes have their
    identifiers resolved to positional semantic addresses via
    ``_Env.resolve``, rather than emitting their raw string as a
    sigma-key param.  Under scope resolution, two functions with
    identical bodies and different local variable names produce
    identical sigma keys for every Name reference, which lets cstz's
    hash-consing merge them into a single Addr0 at ingest time.
    Default False preserves pre-Step-1 behavior exactly.
    """
    ast_type = type(node).__name__
    params = _extract_params(node, env=env, resolve_scopes=resolve_scopes)

    # Bind declarations introduced by this node and select the
    # environment to use for the children.
    child_env = _bind_declarations(node, env)

    # Walk children left-to-right.
    child_addr0_ids: List[str] = []
    for child in ast.iter_child_nodes(node):
        child_addr0_ids.append(
            _walk(child, engine, child_env, filename, rank, patch,
                  resolve_scopes=resolve_scopes)
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
    resolve_scopes: bool = False,
) -> PFFCascadeEngine:
    """Factorize Python source into a populated PFFCascadeEngine.

    ``source`` may be:
      - an ``ast.Module`` object (already-parsed)
      - a ``Path`` or ``str`` pointing at an existing ``.py`` file
      - any other ``str`` is parsed as inline source text

    ``resolve_scopes``: when True, the classifier emits resolved
    positional semantic addresses for Name and ast.arg nodes via
    ``_Env.resolve``, rather than their raw identifier strings.
    Under scope resolution, two functions with identical bodies and
    different local variable names produce identical sigma keys for
    every Name reference, and cstz's existing hash-consing merges
    them into a single Addr0 at ingest time.  This is the
    prerequisite Step 1 of the cstz-on-cstz refactor oracle
    experiment; see rhpf-pff-profiles/AUDIT.md §"Query specification"
    and the enriched plan file for the full DAG.  Default False
    preserves pre-Step-1 behavior exactly.

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
            _walk(stmt, engine, env, display, rank, patch,
                  resolve_scopes=resolve_scopes)
        return engine

    if isinstance(source, Path):
        text = source.read_text()
        tree = ast.parse(text)
        env = _seeded_root_env().child()
        display = filename or source.stem
        for stmt in tree.body:
            _walk(stmt, engine, env, display, rank, patch,
                  resolve_scopes=resolve_scopes)
        return engine

    # str: try as path first, fall back to inline source.
    candidate = Path(source)
    if candidate.is_file():
        text = candidate.read_text()
        tree = ast.parse(text)
        env = _seeded_root_env().child()
        display = filename or candidate.stem
        for stmt in tree.body:
            _walk(stmt, engine, env, display, rank, patch,
                  resolve_scopes=resolve_scopes)
        return engine

    tree = ast.parse(source)
    env = _seeded_root_env()
    display = filename or "<input>"
    for stmt in tree.body:
        _walk(stmt, engine, env, display, rank, patch,
              resolve_scopes=resolve_scopes)
    return engine


__all__ = ["factorize"]
