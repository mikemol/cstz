"""Structural identity via grammar reflection — the engine.

For each of the three parsers (pandoc, tree-sitter-agda, python ast) we
expose a uniform ``NodeAdapter`` interface that gives us:

    node.kind         — the grammar's own type tag (string)
    node.fields       — a list of (field_name_or_None, child_node)
    node.text_tokens  — literal string tokens this node carries
    node.named_decl   — (kind, name) if this node is a declaration, else None
    node.source_path  — origin file path
    node.source_line  — origin line (1-based)

On top of that we compute four operators used by the alignment engine:

    wedge_identity(node)    — Id(A) = d_kind(A) ∧ Id(child_1) ∧ ...
                              in sparse bitmask form (paper Yoneda)
    structural_hash(node)   — recursive hash over (kind, child_hashes);
                              a finer ersatz that preserves order+multiplicity
    tau_profile(node, st)   — bitmask of kind-ids present in subtree
    token_bag(node)         — frozenset of identifier/label tokens

All four are computed by walking the parse tree.  No regex runs over
source text.

Self-hosting: ``wedge_identity`` is the paper's own Id(A) formula
(Rem 3.17, Thm 9.14).  We represent a grade-k element of ∧(GF(2)^n)
as a ``frozenset[int]`` of bitmasks — each bitmask an integer < 2^n
(Python ints are unbounded-precision) where bit i is set iff the i-th
kind contributes.  The wedge of two such elements is
``{s | t for s in F for t in G if (s & t) == 0}`` — O(|F|·|G|),
independent of n.  This is equivalent to ``cstz.exterior.ext_wedge``
under sparse representation: where ``cstz.exterior`` stores the full
``[0]*2^n`` coefficient array, we store only the support.

Structural hash remains alongside because the wedge identity is
coarser: two subtrees with the same multiset of kinds at the same
grades produce the same wedge element, even if their child trees
have different orders.  Structural hash preserves that.
"""

from __future__ import annotations

import ast
import hashlib
import json
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator, Protocol, Sequence, runtime_checkable


# ---------------------------------------------------------------------------
# Symbol table — the basis of V_source
# ---------------------------------------------------------------------------


class SymbolTable:
    """Per-source registry of node kinds, assigning stable one-hot IDs.

    This mirrors ``cstz.classify.registry.DiscriminatorRegistry`` but
    over parser node types instead of runtime predicates.  Each grammar
    tag gets ``id = 1 << k`` in registration order.
    """

    def __init__(self, source: str) -> None:
        self.source = source
        self._by_name: dict[str, int] = {}
        self._ordered: list[str] = []

    def intern(self, kind: str) -> int:
        if kind not in self._by_name:
            self._by_name[kind] = len(self._ordered)
            self._ordered.append(kind)
        return self._by_name[kind]

    def id_of(self, kind: str) -> int:
        return self._by_name[kind]

    def name_of(self, kind_id: int) -> str:
        return self._ordered[kind_id]

    def __len__(self) -> int:
        return len(self._ordered)

    def all(self) -> list[str]:
        return list(self._ordered)


# ---------------------------------------------------------------------------
# NodeAdapter protocol
# ---------------------------------------------------------------------------


@runtime_checkable
class NodeAdapter(Protocol):
    """Uniform parse-tree node interface across the three parsers."""
    source: str
    source_path: str

    @property
    def kind(self) -> str: ...
    @property
    def fields(self) -> list[tuple[str | None, "NodeAdapter"]]: ...
    @property
    def text_tokens(self) -> Iterable[str]: ...
    @property
    def named_decl(self) -> tuple[str, str] | None: ...
    @property
    def source_line(self) -> int: ...


# ---------------------------------------------------------------------------
# Adapters
# ---------------------------------------------------------------------------


@dataclass
class PandocNode:
    """Wraps a pandoc JSON AST node.

    Pandoc JSON nodes are dicts with ``t`` (tag) and ``c`` (content).
    Some tags have structured content (lists, dicts); others are leaves
    with string content.
    """
    source: str = "paper"
    source_path: str = ""
    _json: dict = field(default_factory=dict)
    _line: int = 0

    @property
    def kind(self) -> str:
        t = self._json.get("t", "")
        # Qualify structural containers by their class attribute so
        # "Div.definition" and "Div.theorem" are distinct basis vectors.
        if t == "Div":
            c = self._json.get("c", [])
            if isinstance(c, list) and len(c) == 2 and isinstance(c[0], list) and len(c[0]) == 3:
                classes = c[0][1]
                if classes:
                    return f"Div.{classes[0]}"
        if t == "Header":
            c = self._json.get("c", [])
            if isinstance(c, list) and len(c) >= 1 and isinstance(c[0], int):
                return f"Header.{c[0]}"
        return t

    @property
    def fields(self) -> list[tuple[str | None, "PandocNode"]]:
        c = self._json.get("c")
        out: list[tuple[str | None, PandocNode]] = []
        if isinstance(c, list):
            for child in c:
                if isinstance(child, dict) and "t" in child:
                    out.append((None, PandocNode(source_path=self.source_path, _json=child)))
                elif isinstance(child, list):
                    for sub in child:
                        if isinstance(sub, dict) and "t" in sub:
                            out.append((None, PandocNode(source_path=self.source_path, _json=sub)))
        return out

    @property
    def text_tokens(self) -> Iterable[str]:
        t = self._json.get("t", "")
        c = self._json.get("c")
        if t == "Str" and isinstance(c, str):
            yield c
        elif t == "Code":
            if isinstance(c, list) and len(c) == 2 and isinstance(c[1], str):
                yield c[1]
        elif t == "Math":
            if isinstance(c, list) and len(c) == 2 and isinstance(c[1], str):
                yield c[1]
        elif t == "Span":
            # Spans carry label IDs on \label{…}
            if isinstance(c, list) and len(c) == 2:
                attr = c[0]
                if isinstance(attr, list) and len(attr) == 3:
                    id_ = attr[0]
                    if id_:
                        yield id_
        elif t == "Div":
            if isinstance(c, list) and len(c) == 2:
                attr = c[0]
                if isinstance(attr, list) and len(attr) == 3:
                    id_ = attr[0]
                    if id_:
                        yield id_
        elif t == "Link":
            # \ref{foo} → Link whose url is #foo
            if isinstance(c, list) and len(c) == 3:
                target = c[2]
                if isinstance(target, list) and target and isinstance(target[0], str):
                    yield target[0].lstrip("#")

    @property
    def named_decl(self) -> tuple[str, str] | None:
        t = self._json.get("t", "")
        c = self._json.get("c", [])
        if t == "Div" and isinstance(c, list) and len(c) == 2:
            attr = c[0]
            if isinstance(attr, list) and len(attr) == 3:
                id_, classes, _ = attr
                for cl in classes:
                    if cl in {"definition", "theorem", "proposition", "lemma",
                             "corollary", "remark", "example", "conjecture",
                             "openquestion"}:
                        return (cl, id_ or "")
        return None

    @property
    def source_line(self) -> int:
        return self._line


class TreeSitterAgdaNode:
    """Wraps a tree-sitter-agda Node."""

    def __init__(self, ts_node, source_path: str = "") -> None:
        self._node = ts_node
        self.source = "agda"
        self.source_path = source_path

    @property
    def kind(self) -> str:
        return self._node.type

    @property
    def fields(self) -> list[tuple[str | None, "TreeSitterAgdaNode"]]:
        out: list[tuple[str | None, TreeSitterAgdaNode]] = []
        for ch in self._node.children:
            if not ch.is_named:
                continue
            field_name = self._node.field_name_for_child(self._node.children.index(ch))
            out.append((field_name, TreeSitterAgdaNode(ch, self.source_path)))
        return out

    @property
    def text_tokens(self) -> Iterable[str]:
        kind = self._node.type
        if kind in {"qid", "id", "function_name", "field_name",
                     "module_name", "record_name", "data_name", "constructor_name",
                     "atom"}:
            yield self._node.text.decode("utf-8", errors="replace").strip()

    @property
    def named_decl(self) -> tuple[str, str] | None:
        kind = self._node.type
        if kind == "module":
            mn = _ts_first_named_child(self._node, "module_name")
            if mn is not None:
                return ("module", mn.text.decode("utf-8", errors="replace").strip())
        elif kind == "record":
            rn = _ts_first_named_child(self._node, "record_name")
            if rn is not None:
                return ("record", rn.text.decode("utf-8", errors="replace").strip())
        elif kind == "data":
            dn = _ts_first_named_child(self._node, "data_name") or _ts_first_named_child(self._node, "qid")
            if dn is not None:
                return ("data", dn.text.decode("utf-8", errors="replace").strip())
        elif kind == "function":
            lhs = _ts_first_named_child(self._node, "lhs")
            if lhs is not None:
                fn = _ts_first_named_child(lhs, "function_name")
                if fn is not None:
                    name = fn.text.decode("utf-8", errors="replace").strip()
                    rhs = _ts_first_named_child(self._node, "rhs")
                    if rhs is not None and rhs.text.decode("utf-8", errors="replace").lstrip().startswith(":"):
                        return ("function", name)
        return None

    @property
    def source_line(self) -> int:
        return self._node.start_point[0] + 1


def _ts_first_named_child(node, kind: str):
    for ch in node.children:
        if ch.is_named and ch.type == kind:
            return ch
    return None


class PyAstNode:
    """Wraps a Python ``ast.AST`` node."""

    def __init__(self, py_node: ast.AST, source_path: str = "") -> None:
        self._node = py_node
        self.source = "python"
        self.source_path = source_path

    @property
    def kind(self) -> str:
        return type(self._node).__name__

    @property
    def fields(self) -> list[tuple[str | None, "PyAstNode"]]:
        out: list[tuple[str | None, PyAstNode]] = []
        for name, value in ast.iter_fields(self._node):
            if isinstance(value, ast.AST):
                out.append((name, PyAstNode(value, self.source_path)))
            elif isinstance(value, list):
                for item in value:
                    if isinstance(item, ast.AST):
                        out.append((name, PyAstNode(item, self.source_path)))
        return out

    @property
    def text_tokens(self) -> Iterable[str]:
        n = self._node
        if isinstance(n, ast.Name):
            yield n.id
        elif isinstance(n, ast.arg):
            yield n.arg
        elif isinstance(n, ast.Attribute):
            yield n.attr
        elif isinstance(n, ast.Constant) and isinstance(n.value, str):
            # Docstring / string literal: yield whole value — alignment
            # engine can search for label tokens inside.
            yield n.value
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            yield n.name

    @property
    def named_decl(self) -> tuple[str, str] | None:
        n = self._node
        if isinstance(n, ast.FunctionDef):
            return ("function", n.name)
        if isinstance(n, ast.AsyncFunctionDef):
            return ("function", n.name)
        if isinstance(n, ast.ClassDef):
            return ("class", n.name)
        if isinstance(n, ast.Module):
            return ("module", getattr(n, "_cstz_module_name", ""))
        return None

    @property
    def source_line(self) -> int:
        return getattr(self._node, "lineno", 0)


# ---------------------------------------------------------------------------
# Structural operators (work on any NodeAdapter)
# ---------------------------------------------------------------------------


def structural_hash(node, symtab: SymbolTable) -> str:
    """Recursive hash that preserves order and multiplicity.

    ``hash(node) = hash(kind, tuple(hash(child) for child in children))``.
    Returned as a hex string for stability across Python processes.

    Finer than ``wedge_identity``: two subtrees with the same wedge
    identity can have different structural hashes (e.g. same multiset
    of kinds in different child-index positions).  Use this when you
    need a precise structural fingerprint and ``wedge_identity`` when
    you want the paper's Yoneda-style class equality.
    """
    kind = node.kind
    symtab.intern(kind)
    child_hashes: list[str] = []
    for fname, child in node.fields:
        child_hashes.append(f"{fname or ''}:{structural_hash(child, symtab)}")
    h = hashlib.blake2b(digest_size=16)
    h.update(kind.encode("utf-8"))
    h.update(b"|")
    h.update("||".join(child_hashes).encode("utf-8"))
    return h.hexdigest()


# ---------------------------------------------------------------------------
# Sparse exterior algebra — the paper's Id(A) via bitmask-int wedge
# ---------------------------------------------------------------------------
#
# An element of ∧(GF(2)^n) is represented as a ``frozenset[int]``.  Each
# element of the set is an integer < 2^n whose bits encode the subset of
# basis vectors in that basis k-vector.  GF(2) coefficients are implicit:
# a basis k-vector is "on" iff it appears in the set (coeff 1), "off" iff
# absent (coeff 0).  This is the bitmask-indexed sparse analogue of
# ``cstz.exterior``'s dense [0]*2^n representation; the algebra is
# identical, only the storage differs.

WedgeElement = frozenset  # frozenset[int]


def sparse_wedge(f: WedgeElement, g: WedgeElement) -> WedgeElement:
    """Wedge product of two sparse exterior elements.

    Implements ``h[s|t] ^= f[s] & g[t]`` for ``s & t == 0``:
    for each disjoint pair (s, t) in F × G, XOR in s|t to the result.
    Equivalent to ``cstz.exterior.ext_wedge`` under sparse semantics.
    """
    result: set[int] = set()
    for s in f:
        for t in g:
            if (s & t) == 0:
                union = s | t
                if union in result:
                    result.discard(union)  # XOR: 1^1 = 0
                else:
                    result.add(union)
    return frozenset(result)


def sparse_basis(kind_id: int) -> WedgeElement:
    """Grade-1 basis element: the mask 1 << kind_id."""
    return frozenset({1 << kind_id})


def sparse_zero() -> WedgeElement:
    return frozenset()


def sparse_is_zero(f: WedgeElement) -> bool:
    return not f


def wedge_identity(node, symtab: SymbolTable) -> WedgeElement:
    """Id(A) = d_kind(A) ∧ Id(child_1) ∧ Id(child_2) ∧ …

    The paper's Yoneda structural-identity (Rem 3.17, Thm 9.14) as a
    sparse exterior-algebra element over the grammar's symbol table.
    Two subtrees that produce the same ``WedgeElement`` are
    κ-equivalent in the paper's framework.

    Note: because the wedge product over GF(2) is nilpotent
    (``d ∧ d = 0``), a subtree containing the same kind twice at the
    same grade produces zero for that term — which is the correct
    parity-sensitive equivalence relation.  This is STRICTLY coarser
    than ``structural_hash``, which does not collapse repeats.
    """
    kind_id = symtab.intern(node.kind)
    acc = sparse_basis(kind_id)
    for _, child in node.fields:
        child_id = wedge_identity(child, symtab)
        acc = sparse_wedge(acc, child_id)
        if sparse_is_zero(acc):
            # Early termination: once zero, the full wedge is zero.
            return acc
    return acc


def tau_profile(node, symtab: SymbolTable) -> int:
    """Bitmask of kind-ids present in the subtree rooted at ``node``.

    Each distinct kind contributes one bit; repeats don't change the
    bitmask (mirroring the wedge product's nilpotency, ``d ∧ d = 0``,
    where a kind that appears twice cancels → tracked separately via
    multiplicity if needed).
    """
    bit = 1 << symtab.intern(node.kind)
    mask = bit
    for _, child in node.fields:
        mask |= tau_profile(child, symtab)
    return mask


def deep_kind_set(node) -> frozenset[str]:
    """Every kind appearing in the full subtree rooted at ``node``.

    Kinds are returned VERBATIM (not lowercased, not canonicalized).
    Earlier versions lowercased to expose accidental cross-source
    matches (Python ``FunctionDef`` vs Agda ``function``); user
    feedback made clear this is a hardcoded equivalence assertion
    that the pipeline shouldn't bake in.  Any such equivalence
    should EMERGE from residue-driven wedge discovery, not be
    asserted at registration time.

    The set representation is chosen over a multiset intentionally:
    we want MEMBERSHIP (does this kind appear) not count, matching
    the grade-1 wedge semantics.
    """
    out: set[str] = {node.kind}
    for _fname, child in node.fields:
        out |= deep_kind_set(child)
    return frozenset(out)


def deep_edge_set(node) -> frozenset[tuple[str, str]]:
    """Every (parent_kind, child_kind) edge in the subtree (verbatim)."""
    out: set[tuple[str, str]] = set()
    for _fname, child in node.fields:
        out.add((node.kind, child.kind))
        out |= deep_edge_set(child)
    return frozenset(out)


def token_bag(node) -> frozenset[str]:
    """Collect every leaf text token in the subtree rooted at ``node``.

    The exact definition of "leaf text token" is parser-specific
    (see each adapter's ``text_tokens`` property).  We collect strings
    of length ≥ 2 to avoid flooding with single-character atoms.
    """
    out: set[str] = set()
    out.update(t for t in node.text_tokens if t and len(t) >= 2)
    for _, child in node.fields:
        out |= token_bag(child)
    return frozenset(out)


def child_signature(node) -> list[tuple[str | None, str]]:
    """Direct children as (field_name, kind) pairs.

    This is the raw material for residue drilldown: when two objects
    share a tau_profile but differ structurally, the first index where
    child_signature differs is the κ-evolution target.
    """
    return [(fname, child.kind) for fname, child in node.fields]


def adjacency_profile(node, symtab: SymbolTable) -> frozenset[tuple[int, int]]:
    """Grade-2 exterior profile: every (parent_kind_id, child_kind_id) edge.

    In the paper's framework (§6, Def 6.2), a morphism ``f: a → b`` is
    a grade-1 discriminator applied across two grade-1 objects.
    Lifted to structural identity: for each parent-child edge in the
    parse tree, emit the pair (parent_kind_id, child_kind_id).  The
    resulting frozenset IS the grade-2 part of the subtree's identity.

    Semantically: two decls with similar grade-2 adjacency profiles
    use similar PATTERNS of parent-child relationships, independent
    of which specific names or tokens appear.  This is the relational
    discriminator missing from grade-1-only analysis.

    Under cross-source alignment, adjacency IDs are not directly
    comparable (different parsers, different kind_ids), but the
    *distribution* and *cardinality* of the adjacency profile IS a
    meaningful cross-source signal.
    """
    edges: set[tuple[int, int]] = set()

    def rec(n):
        parent_id = symtab.intern(n.kind)
        for _, child in n.fields:
            child_id = symtab.intern(child.kind)
            edges.add((parent_id, child_id))
            rec(child)

    rec(node)
    return frozenset(edges)


def field_adjacency_profile(node, symtab: SymbolTable) -> frozenset[tuple[int, str, int]]:
    """Grade-2 with field labels: (parent_kind, field_name, child_kind) triples.

    Finer than ``adjacency_profile``: distinguishes ``FunctionDef/args/arguments``
    from ``FunctionDef/body/arguments`` (hypothetical), both of which
    have the same (parent, child) but different edge labels.

    The field edges come from each parser's native field mapping —
    tree-sitter-agda's ``field_name_for_child``, Python ast's
    ``_fields``, pandoc's JSON schema.  No hand-written label set.
    """
    edges: set[tuple[int, str, int]] = set()

    def rec(n):
        parent_id = symtab.intern(n.kind)
        for fname, child in n.fields:
            child_id = symtab.intern(child.kind)
            edges.add((parent_id, fname or "", child_id))
            rec(child)

    rec(node)
    return frozenset(edges)


# ---------------------------------------------------------------------------
# Top-level parsers (source files → list of named-decl adapters)
# ---------------------------------------------------------------------------


def parse_paper_decls(paper_root: Path) -> Iterator[PandocNode]:
    """Yield one PandocNode per theorem-like Div in ``paper_root``.

    Uses the same pandoc invocation as ``scripts/extract_paper.py``.
    """
    result = subprocess.run(
        ["pandoc", "-f", "latex", "-t", "json", "main.tex"],
        cwd=paper_root,
        capture_output=True,
        check=True,
    )
    doc = json.loads(result.stdout)

    def walk(node, path="paper/main.tex"):
        if isinstance(node, list):
            for item in node:
                yield from walk(item, path)
        elif isinstance(node, dict):
            pn = PandocNode(source_path=path, _json=node)
            if pn.named_decl is not None:
                yield pn
                # Don't descend into theorem-body — declarations inside a proof
                # are not top-level.
                return
            c = node.get("c")
            if isinstance(c, (list, dict)):
                yield from walk(c, path)

    yield from walk(doc.get("blocks", []))


class _TreeSitterAgdaModuleWithBody:
    """Wrap a tree-sitter-agda module declaration so its ``fields``
    include all subsequent top-level siblings in the same source_file.

    Tree-sitter-agda represents ``module X where`` as a bare declaration;
    its body (postulate blocks, function decls, etc.) are emitted as
    SIBLINGS at the source_file root, not as children.  For alignment,
    we want the module to "own" its file's contents so its deep_kinds
    reflect the full scope.  This wrapper delegates ``kind``,
    ``named_decl``, ``source_line``, and ``text_tokens`` to the
    underlying module node, but overrides ``fields`` to return the
    module's own named children PLUS the trailing file-level siblings.
    """

    def __init__(self, module_node, file_siblings, source_path: str):
        self._node = module_node
        self._siblings = file_siblings
        self.source = "agda"
        self.source_path = source_path

    @property
    def kind(self) -> str:
        return "module"

    @property
    def fields(self):
        out = []
        for ch in self._node.children:
            if ch.is_named:
                out.append((None, TreeSitterAgdaNode(ch, self.source_path)))
        for sib in self._siblings:
            if sib.is_named:
                out.append((None, TreeSitterAgdaNode(sib, self.source_path)))
        return out

    @property
    def text_tokens(self):
        return TreeSitterAgdaNode(self._node, self.source_path).text_tokens

    @property
    def named_decl(self):
        return TreeSitterAgdaNode(self._node, self.source_path).named_decl

    @property
    def source_line(self) -> int:
        return self._node.start_point[0] + 1


def parse_agda_decls(path: Path) -> Iterator:
    """Yield one TreeSitterAgdaNode per top-level declaration in ``path``.

    Agda modules own their file — for module decls we wrap them so that
    ``fields`` returns the subsequent top-level siblings (postulate /
    function / record / data declarations declared inside the module's
    scope) as if they were children.  That lets deep_kind_set /
    deep_edge_set see the full structural content of the file, which
    is what we want for alignment.
    """
    import tree_sitter_agda
    from tree_sitter import Language, Parser
    lang = Language(tree_sitter_agda.language())
    parser = Parser(lang)
    src = path.read_bytes()
    tree = parser.parse(src)
    root = tree.root_node
    rel_path = str(path)

    # Identify the module node and collect all top-level siblings that
    # come after it (those are the module's content per Agda scoping).
    children = list(root.children)
    module_idx = None
    for i, ch in enumerate(children):
        if ch.type == "module":
            module_idx = i
            break
    siblings_after_module = children[module_idx + 1:] if module_idx is not None else []

    for i, ch in enumerate(children):
        if ch.type == "module":
            wrapped = _TreeSitterAgdaModuleWithBody(
                ch, siblings_after_module, rel_path
            )
            if wrapped.named_decl is not None:
                yield wrapped
        elif ch.type in ("record", "data", "function", "postulate"):
            node = TreeSitterAgdaNode(ch, rel_path)
            if node.named_decl is not None:
                yield node


def parse_python_decls(path: Path) -> Iterator[PyAstNode]:
    """Yield one PyAstNode per top-level declaration in ``path``."""
    src = path.read_text()
    tree = ast.parse(src, filename=str(path))
    tree._cstz_module_name = path.stem  # for PyAstNode.named_decl
    yield PyAstNode(tree, str(path))
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            yield PyAstNode(node, str(path))


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------


if __name__ == "__main__":  # pragma: no cover
    import sys
    repo = Path.cwd()
    st_paper = SymbolTable("paper")
    st_agda = SymbolTable("agda")
    st_py = SymbolTable("python")

    if "--paper" in sys.argv:
        for n in parse_paper_decls(repo / "paper"):
            kind, name = n.named_decl
            print(f"paper  {kind:10s} {name[:40]:40s} hash={structural_hash(n, st_paper)[:12]}  tokens={len(token_bag(n))}")
    if "--agda" in sys.argv:
        for p in sorted((repo / "agda").rglob("*.agda"))[:3]:
            for n in parse_agda_decls(p):
                kind, name = n.named_decl
                print(f"agda   {kind:10s} {name[:40]:40s} hash={structural_hash(n, st_agda)[:12]}")
    if "--python" in sys.argv:
        for p in sorted((repo / "src/cstz").rglob("*.py"))[:3]:
            for n in parse_python_decls(p):
                dc = n.named_decl
                if dc is None: continue
                kind, name = dc
                print(f"python {kind:10s} {name[:40]:40s} hash={structural_hash(n, st_py)[:12]}")

    print(f"\nSymbol-table sizes: paper={len(st_paper)} agda={len(st_agda)} python={len(st_py)}")
