"""Python AST → SPPF classifier.

Walks a Python AST, infers dependent types, classifies categorical
constructions via τ×σ → κ, and feeds nodes into an SPPF.

Usage::

    from cstz import factorize

    sppf = factorize("path/to/source.py")
    print(sppf.summary())
"""

import ast
import hashlib
from pathlib import Path

from .core import SPPF


# ── Type inference tables ────────────────────────────────────────────

_KNOWN_TYPES = {
    "Graph": "Graph", "URIRef": "URIRef", "BNode": "BNode",
    "Literal": "Literal", "Namespace": "NS",
    "RDF": "RDF", "RDFS": "RDFS", "SH": "SH", "XSD": "XSD",
    "ast": "ast", "Path": "Path",
    "LG": "NS", "short": "→str", "resolve": "→URIRef",
    "local_name": "→str", "new_graph": "→Graph",
    "str": "str", "int": "int", "float": "float", "bool": "bool",
    "list": "list", "dict": "dict", "set": "set", "tuple": "tuple",
    "len": "→int", "sorted": "→list", "isinstance": "→bool",
    "next": "→T", "print": "→None", "repr": "→str",
    "hasattr": "→bool", "getattr": "→T",
}

_RECV_ATTR = {
    ("RDF", "type"): "URIRef", ("RDFS", "label"): "URIRef",
    ("RDFS", "domain"): "URIRef", ("RDFS", "range"): "URIRef",
    ("RDFS", "subClassOf"): "URIRef", ("RDFS", "Class"): "URIRef",
    ("SH", "select"): "URIRef", ("NS", "*"): "URIRef",
    ("Path", "parent"): "Path", ("Path", "stem"): "str",
    ("Path", "name"): "str",
}

_METHOD_RET = {
    "add": "None", "remove": "None", "append": "None", "extend": "None",
    "objects": "Iter", "subjects": "Iter", "triples": "Iter",
    "predicate_objects": "Iter", "subject_predicates": "Iter",
    "query": "Result", "parse": "Graph", "bind": "None",
    "get": "T", "items": "Iter", "keys": "Iter", "values": "Iter",
    "startswith": "bool", "endswith": "bool", "split": "list",
    "rsplit": "list", "strip": "str", "join": "str",
    "glob": "Iter", "is_dir": "bool", "read_text": "str",
}

_PARAM_TYPES = {
    "g": "Graph", "self": "Self", "node": "AST",
    "kernel": "Kernel", "uri": "URIRef", "subj": "URIRef",
    "full": "Graph",
}


# ── Type environment ─────────────────────────────────────────────────

class _Env:
    __slots__ = ('_bindings', '_parent')

    def __init__(self, parent=None):
        self._bindings = {}
        self._parent = parent

    def bind(self, name, typ):
        self._bindings[name] = typ

    def get(self, name):
        if name in self._bindings:
            return self._bindings[name]
        if self._parent:
            return self._parent.get(name)
        return _KNOWN_TYPES.get(name)

    def child(self):
        return _Env(self)


def _infer(node, env):
    """Infer the dependent type of an AST node within an environment."""
    if isinstance(node, ast.Name):
        return env.get(node.id)
    if isinstance(node, ast.Attribute):
        rt = _infer(node.value, env)
        a = node.attr
        if rt:
            k = (rt, a)
            if k in _RECV_ATTR:
                return _RECV_ATTR[k]
            w = (rt, "*")
            if w in _RECV_ATTR:
                return _RECV_ATTR[w]
            return f"{rt}.{a}"
        return None
    if isinstance(node, ast.Call):
        ft = _infer(node.func, env)
        if ft and ft.startswith("→"):
            return ft[1:]
        if ft and "." in ft:
            m = ft.rsplit(".", 1)[-1]
            if m in _METHOD_RET:
                return _METHOD_RET[m]
        return None
    if isinstance(node, ast.Constant):
        v = node.value
        if v is None: return "NoneType"
        if isinstance(v, bool): return "bool"
        if isinstance(v, int): return "int"
        if isinstance(v, float): return "float"
        if isinstance(v, str): return "str"
        return None
    if isinstance(node, ast.List): return "list"
    if isinstance(node, ast.Dict): return "dict"
    if isinstance(node, ast.Set): return "set"
    if isinstance(node, ast.Tuple): return "tuple"
    if isinstance(node, ast.JoinedStr): return "str"
    return None


# ── Categorical classification (κ = g(τ,σ)) ─────────────────────────

def _receiver_domain(rt):
    """Map a raw receiver type to a semantic domain for κ-tag qualification."""
    if rt is None:
        return "?"
    if "Graph" in rt:
        return "graph"
    if rt.startswith("Self.") or rt == "Self":
        return "state"
    if rt.startswith("Kernel"):
        return "kernel"
    if rt.startswith("AST") or rt == "ast":
        return "syntax"
    if rt in ("str", "bytes") or rt.startswith("str."):
        return "string"
    if rt in ("list", "tuple") or rt.startswith("list.") or rt.startswith("tuple."):
        return "sequence"
    if rt in ("dict",) or rt.startswith("dict."):
        return "mapping"
    if rt in ("set", "frozenset") or rt.startswith("set."):
        return "collection"
    if rt in ("int", "float", "bool", "NoneType"):
        return "scalar"
    if rt.startswith("→"):
        return "arrow"
    return "object"


def _classify_kappa(node, env):
    """Classify an AST node by its universal construction.

    Returns a κ-tag that is the product τ×σ → Construction.
    """
    if isinstance(node, ast.Constant):
        return "terminal"
    if isinstance(node, ast.Name):
        ctx = type(node.ctx).__name__
        if ctx == "Store":
            return "bind"
        t = env.get(node.id)
        if t and t.startswith("→"):
            return "arrow"
        return "var"
    if isinstance(node, ast.Attribute):
        rt = _infer(node.value, env)
        attr = node.attr
        domain = _receiver_domain(rt)
        if rt in ("NS", "RDF", "RDFS", "SH", "XSD"):
            return "representable"
        if attr in ("add", "remove"):
            return f"monoid.op@{domain}"
        if attr in ("append", "extend"):
            return f"free_monoid.op@{domain}"
        if attr in ("objects", "subjects", "triples",
                     "predicate_objects", "subject_predicates"):
            return f"pullback@{domain}"
        if attr == "query":
            return f"image@{domain}"
        if attr in ("startswith", "endswith", "__contains__"):
            return "subobject"
        if attr in ("split", "rsplit"):
            return "coproduct"
        if attr == "join":
            return "free_monoid.fold"
        if attr in ("items", "keys", "values"):
            return f"projection@{domain}"
        if attr == "get":
            return f"partial@{domain}"
        if attr == "type":
            return "classifier"
        return f"morphism@{domain}"
    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name):
            name = node.func.id
            if name == "isinstance": return "fiber"
            if name == "set": return "powerset"
            if name == "dict": return "exponential"
            if name == "list": return "free_monoid"
            if name == "sorted": return "total_order"
            if name == "len": return "cardinality"
            if name == "next": return "unit"
            if name == "print": return "effect"
            if name in ("str", "int", "float", "bool"): return "coerce"
            if name in ("URIRef", "BNode", "Literal"): return "inject"
            if name == "Namespace": return "representable.new"
            if name == "hasattr": return "subobject"
            if name == "getattr": return "eval"
        if isinstance(node.func, ast.Attribute):
            attr = node.func.attr
            rt = _infer(node.func.value, env)
            domain = _receiver_domain(rt)
            if attr == "add":
                if rt and "Graph" in (rt or ""):
                    return "graph.emit"
                if rt == "set":
                    return "powerset.insert"
                return f"monoid.op@{domain}"
            if attr == "append": return f"free_monoid.snoc@{domain}"
            if attr in ("objects", "subjects", "triples"):
                return f"pullback.query@{domain}"
            if attr == "query": return f"image.compute@{domain}"
            if attr == "parse": return "left_adjoint"
            if attr == "bind": return "equip"
            if attr in ("startswith", "endswith"): return "subobject.test"
            if attr == "join": return "free_monoid.fold"
            if attr in ("split", "rsplit"): return "coproduct.decompose"
            if attr == "get": return f"partial.apply@{domain}"
            if attr in ("items", "keys", "values"): return f"projection.compute@{domain}"
            if attr == "format": return "free_monoid.fold"
        return "apply"
    if isinstance(node, ast.Assign): return "let"
    if isinstance(node, ast.AugAssign): return "monoid.accum"
    if isinstance(node, ast.For): return "fold"
    if isinstance(node, ast.While): return "fixpoint"
    if isinstance(node, ast.If):
        if isinstance(node.test, ast.Call) and isinstance(node.test.func, ast.Name):
            if node.test.func.id == "isinstance":
                return "coproduct.elim"
        if isinstance(node.test, ast.Compare):
            return "equalizer"
        if isinstance(node.test, ast.UnaryOp) and isinstance(node.test.op, ast.Not):
            return "complement"
        return "coproduct.elim"
    if isinstance(node, ast.Return): return "terminal.map"
    if isinstance(node, ast.Tuple):
        ctx = type(node.ctx).__name__ if hasattr(node, 'ctx') else "Load"
        return "product.unpack" if ctx == "Store" else "product"
    if isinstance(node, ast.List): return "free_monoid.literal"
    if isinstance(node, ast.Dict): return "exponential.literal"
    if isinstance(node, ast.Set): return "powerset.literal"
    if isinstance(node, ast.ListComp): return "free_monoid.map"
    if isinstance(node, ast.SetComp): return "powerset.map"
    if isinstance(node, ast.DictComp): return "exponential.map"
    if isinstance(node, ast.GeneratorExp): return "lazy_fold"
    if isinstance(node, ast.BoolOp):
        return "meet" if isinstance(node.op, ast.And) else "join"
    if isinstance(node, ast.Compare): return "equalizer"
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Add): return "monoid.op"
        if isinstance(node.op, ast.Mod): return "quotient"
        return "bimap"
    if isinstance(node, ast.UnaryOp):
        return "complement" if isinstance(node.op, ast.Not) else "endomorphism"
    if isinstance(node, ast.JoinedStr): return "free_monoid.fold"
    if isinstance(node, ast.FormattedValue): return "coerce"
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return "exponential.intro"
    if isinstance(node, ast.ClassDef): return "classifier.intro"
    if isinstance(node, ast.ImportFrom): return "pullback.import"
    if isinstance(node, ast.Expr): return "effect.seq"
    if isinstance(node, ast.Raise): return "initial"
    if isinstance(node, ast.Try): return "coproduct.handle"
    if isinstance(node, ast.With): return "monad.bind"
    if isinstance(node, ast.Yield): return "cofree"
    if isinstance(node, ast.Continue): return "fixpoint.next"
    if isinstance(node, ast.Break): return "fixpoint.halt"
    if isinstance(node, ast.Pass): return "identity"
    return type(node).__name__.lower()


# ── AST node wrapper ─────────────────────────────────────────────────

def _extract_params(node):
    """Extract the syntactic parameters of an AST node."""
    params = {}
    if isinstance(node, ast.Name):
        params["n"] = node.id
    elif isinstance(node, ast.Attribute):
        params["a"] = node.attr
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        params["n"] = node.name
    elif isinstance(node, ast.ClassDef):
        params["n"] = node.name
    elif isinstance(node, ast.Constant):
        v = repr(node.value)
        params["v"] = v if len(v) <= 80 else hashlib.md5(v.encode()).hexdigest()[:12]
    elif isinstance(node, ast.arg):
        params["n"] = node.arg
    elif isinstance(node, ast.alias):
        params["n"] = node.name
    elif isinstance(node, ast.ImportFrom):
        params["m"] = node.module or ""
    elif isinstance(node, ast.keyword):
        if node.arg:
            params["n"] = node.arg
    return tuple(sorted(params.items()))


# ── Recursive AST → SPPF ────────────────────────────────────────────

def _build_sppf(tree, sppf, env, filename="<input>"):
    """Recursively factorize an AST node into the SPPF.
    Returns (sigma_id, tau_id, kappa_id).
    """
    ast_type = type(tree).__name__
    params = _extract_params(tree)
    dep_type = _infer(tree, env)
    kappa_tag = _classify_kappa(tree, env)

    child_env = env
    if isinstance(tree, (ast.FunctionDef, ast.AsyncFunctionDef)):
        child_env = env.child()
        for arg in tree.args.args:
            pt = _PARAM_TYPES.get(arg.arg)
            if pt:
                child_env.bind(arg.arg, pt)
    elif isinstance(tree, ast.ClassDef):
        child_env = env.child()
    elif isinstance(tree, ast.ImportFrom):
        for alias in (tree.names or []):
            nm = alias.asname or alias.name
            if nm in _KNOWN_TYPES:
                env.bind(nm, _KNOWN_TYPES[nm])
    elif isinstance(tree, ast.Assign):
        if len(tree.targets) == 1 and isinstance(tree.targets[0], ast.Name):
            vt = _infer(tree.value, env)
            if vt:
                env.bind(tree.targets[0].id, vt)

    child_results = []
    for child in ast.iter_child_nodes(tree):
        child_results.append(_build_sppf(child, sppf, child_env, filename))

    child_sigmas = tuple(cr[0] for cr in child_results)
    child_taus = tuple(cr[1] for cr in child_results)
    child_kappas = tuple(cr[2] for cr in child_results)

    sid, tid, kid, _ = sppf._ingest_node(
        ast_type, params, dep_type, kappa_tag,
        child_sigmas, child_taus, child_kappas,
        getattr(tree, 'lineno', 0), filename,
    )

    return (sid, tid, kid)


# ── Public API ───────────────────────────────────────────────────────

def factorize(source, extra_types=None):
    """Factorize Python source into a three-fiber SPPF.

    Parameters
    ----------
    source : str or Path or ast.Module
        Python source text, path to a .py file, a directory of .py files,
        or a pre-parsed AST.
    extra_types : dict, optional
        Additional {name: type_string} bindings for the type environment.

    Returns
    -------
    SPPF
    """
    sppf = SPPF()
    env = _Env()
    for k, v in _KNOWN_TYPES.items():
        env.bind(k, v)
    if extra_types:
        for k, v in extra_types.items():
            env.bind(k, v)

    if isinstance(source, ast.Module):
        for stmt in source.body:
            _build_sppf(stmt, sppf, env)
        return sppf

    source = Path(source) if not isinstance(source, Path) else source

    if source.is_dir():
        for pyfile in sorted(source.glob("**/*.py")):
            if pyfile.name == "__init__.py":
                continue
            try:
                tree = ast.parse(pyfile.read_text())
            except (SyntaxError, UnicodeDecodeError):
                continue
            file_env = env.child()
            for stmt in tree.body:
                _build_sppf(stmt, sppf, file_env, pyfile.stem)
        return sppf

    if source.is_file():
        tree = ast.parse(source.read_text())
        file_env = env.child()
        for stmt in tree.body:
            _build_sppf(stmt, sppf, file_env, source.stem)
        return sppf

    # Assume it's source text
    tree = ast.parse(str(source))
    for stmt in tree.body:
        _build_sppf(stmt, sppf, env)
    return sppf
