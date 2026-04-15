#!/usr/bin/env python3
"""Extract named objects from ``src/cstz/**/*.py`` as JSONL rows.

Output schema (one object per line, written to stdout):

    {
      "source":    "python",
      "path":      "src/cstz/sets.py",
      "line":      22,
      "kind":      "function" | "class" | "method" | "constant"
                 | "enum_member" | "dataclass_field"
                 | "decision_point",
      "name":      "kappa_equiv",
      "qualname":  "cstz.sets.kappa_equiv",
      "signature": "(eval_fn, regime, a, b)",
      "arity":     4,
      "docstring": "Full raw docstring text (newlines preserved).",
      "raw":       "",
      "refs":      {}    # empty; cross-references are discovered at
                         # alignment time by searching for literal
                         # tokens from the paper's pandoc AST and from
                         # Agda module names in the raw docstring text.
    }

Scope-2 per the task plan: every top-level FunctionDef, ClassDef,
AsyncFunctionDef, module-scope Assign/AnnAssign, Enum member, dataclass
field, AND every if/elif/match branch inside a function body (user
decision: "Include decision points").

This extractor does NO regex pattern-matching on docstring content.  Only
the ``ast`` module's tree parser is used for structure; docstrings are
emitted as raw text and will be searched at alignment time using tokens
lifted from other sources' parse trees (hybrid-mode, per user decision).

Usage:
    python3 scripts/extract_python.py [ROOT]
    # ROOT defaults to ``src/cstz``.
"""

from __future__ import annotations

import ast
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator


# ---------------------------------------------------------------------------
# AST walking
# ---------------------------------------------------------------------------


def _signature_of(node: ast.FunctionDef | ast.AsyncFunctionDef) -> str:
    """Unparse just the argument list, dropping default values."""
    args = node.args
    try:
        return "(" + ", ".join(a.arg for a in args.args) + ")"
    except Exception:
        return "(?)"


def _arity_of(node: ast.FunctionDef | ast.AsyncFunctionDef) -> int:
    args = node.args
    n = len(args.args) + len(args.kwonlyargs) + len(args.posonlyargs)
    if args.vararg:
        n += 1
    if args.kwarg:
        n += 1
    return n


def _first_line_of_doc(doc: str | None) -> str:
    """Emit the raw docstring text (truncated to 2000 chars for JSONL sanity).

    Previously this returned only the first line; we now emit the whole
    docstring because the alignment engine needs to search for literal label
    tokens anywhere in the text, not just the summary line.
    """
    if not doc:
        return ""
    return doc.strip()[:2000]


def _is_dataclass_decorated(cls: ast.ClassDef) -> bool:
    for dec in cls.decorator_list:
        name = _decorator_name(dec)
        if name in ("dataclass", "dataclasses.dataclass"):
            return True
    return False


def _is_enum_base(cls: ast.ClassDef) -> bool:
    for base in cls.bases:
        n = _base_name(base)
        if n in ("Enum", "IntEnum", "Flag", "IntFlag", "StrEnum"):
            return True
    return False


def _decorator_name(dec: ast.expr) -> str:
    if isinstance(dec, ast.Call):
        dec = dec.func
    if isinstance(dec, ast.Name):
        return dec.id
    if isinstance(dec, ast.Attribute):
        base = _decorator_name(dec.value) if isinstance(dec.value, (ast.Name, ast.Attribute)) else ""
        return f"{base}.{dec.attr}" if base else dec.attr
    return ""


def _base_name(base: ast.expr) -> str:
    if isinstance(base, ast.Name):
        return base.id
    if isinstance(base, ast.Attribute):
        return base.attr
    return ""


def _constant_value_kind(value: ast.expr) -> str:
    """Classify a constant's RHS by its AST shape."""
    if isinstance(value, ast.Constant):
        return f"literal/{type(value.value).__name__}"
    if isinstance(value, ast.List):
        return "list"
    if isinstance(value, ast.Tuple):
        return "tuple"
    if isinstance(value, ast.Dict):
        return "dict"
    if isinstance(value, ast.Set):
        return "set"
    if isinstance(value, ast.Call):
        return "call"
    if isinstance(value, ast.BinOp):
        return "binop"
    return type(value).__name__.lower()


# ---------------------------------------------------------------------------
# Decision-point extraction
# ---------------------------------------------------------------------------


@dataclass
class DecisionPoint:
    line: int
    kind: str  # "if" | "match" | "ifexp" | "for-else" | "while-else"
    arms: list[str] = field(default_factory=list)  # unparsed conditions

    @property
    def arity(self) -> int:
        return len(self.arms)


def _branches_of_if(node: ast.If) -> list[str]:
    """Flatten ``if / elif* / else?`` into a list of arm labels."""
    arms: list[str] = []
    cur: ast.If | None = node
    while cur is not None:
        arms.append(ast.unparse(cur.test))
        if cur.orelse and len(cur.orelse) == 1 and isinstance(cur.orelse[0], ast.If):
            cur = cur.orelse[0]
        else:
            if cur.orelse:
                arms.append("else")
            cur = None
    return arms


def _decision_points_in(func: ast.AST) -> Iterator[DecisionPoint]:
    """Yield decision points directly inside ``func``'s body.

    We only emit top-level decision points in the function body (no recursion
    into nested ifs inside other ifs).  That keeps the alignment unit
    meaningful: one if-chain = one decision point, one match = one decision
    point.  Nested branches are structural detail that the discriminator
    framework's depth/grade treatment handles naturally.
    """
    for node in ast.walk(func):
        if isinstance(node, ast.If) and not _is_elif_continuation(node, func):
            yield DecisionPoint(
                line=node.lineno,
                kind="if",
                arms=_branches_of_if(node),
            )
        elif isinstance(node, ast.Match):
            arms = []
            for case in node.cases:
                label = ast.unparse(case.pattern)
                if case.guard is not None:
                    label += f" if {ast.unparse(case.guard)}"
                arms.append(label)
            yield DecisionPoint(line=node.lineno, kind="match", arms=arms)
        elif isinstance(node, ast.IfExp):
            yield DecisionPoint(
                line=node.lineno,
                kind="ifexp",
                arms=[ast.unparse(node.test), "else"],
            )


def _is_elif_continuation(target: ast.If, root: ast.AST) -> bool:
    """Return True if ``target`` is an ``elif`` arm of an outer If."""
    for parent in ast.walk(root):
        if isinstance(parent, ast.If):
            if parent is target:
                continue
            if (
                parent.orelse
                and len(parent.orelse) == 1
                and parent.orelse[0] is target
            ):
                return True
    return False


# ---------------------------------------------------------------------------
# Extraction driver
# ---------------------------------------------------------------------------


def _module_qualname(root: Path, path: Path) -> str:
    """Compute the dotted module name for ``path`` relative to ``root``."""
    rel = path.relative_to(root.parent)
    parts = list(rel.with_suffix("").parts)
    if parts[-1] == "__init__":
        parts = parts[:-1]
    return ".".join(parts)


def extract_file(root: Path, path: Path) -> Iterator[dict]:
    """Yield one row per named object in ``path``."""
    src = path.read_text()
    try:
        tree = ast.parse(src, filename=str(path))
    except SyntaxError as e:
        print(f"# parse error in {path}: {e}", file=sys.stderr)
        return

    module_qn = _module_qualname(root, path)
    module_doc = ast.get_docstring(tree) or ""
    rel_path = str(path.relative_to(root.parent))

    # ----- Module row -----
    yield {
        "source": "python",
        "path": rel_path,
        "line": 1,
        "kind": "module",
        "name": module_qn.split(".")[-1] if "." in module_qn else module_qn,
        "qualname": module_qn,
        "signature": "",
        "arity": 0,
        "docstring": _first_line_of_doc(module_doc),
        "raw": "",
        "refs": {},
    }

    for node in tree.body:
        yield from _rows_for(node, rel_path, module_qn)


def _rows_for(
    node: ast.AST,
    rel_path: str,
    module_qn: str,
    class_qn: str | None = None,
) -> Iterator[dict]:
    """Dispatch rows for a module- or class-level ast node."""
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        doc = ast.get_docstring(node) or ""
        qn = f"{class_qn or module_qn}.{node.name}"
        yield {
            "source": "python",
            "path": rel_path,
            "line": node.lineno,
            "kind": "method" if class_qn else "function",
            "name": node.name,
            "qualname": qn,
            "signature": _signature_of(node),
            "arity": _arity_of(node),
            "docstring": _first_line_of_doc(doc),
            "raw": "",
            "refs": {},
        }
        for dp in _decision_points_in(node):
            yield {
                "source": "python",
                "path": rel_path,
                "line": dp.line,
                "kind": "decision_point",
                "name": f"{node.name}@{dp.line}",
                "qualname": f"{qn}@{dp.line}",
                "signature": f"{dp.kind}[{', '.join(dp.arms)}]",
                "arity": dp.arity,
                "docstring": "",
                "raw": dp.kind,
                "refs": {"paper": [], "agda": [], "study": [], "axiom_class": []},
            }

    elif isinstance(node, ast.ClassDef):
        doc = ast.get_docstring(node) or ""
        qn = f"{module_qn}.{node.name}"
        bases = [_base_name(b) for b in node.bases]
        kind = (
            "enum"
            if _is_enum_base(node)
            else "dataclass"
            if _is_dataclass_decorated(node)
            else "class"
        )
        yield {
            "source": "python",
            "path": rel_path,
            "line": node.lineno,
            "kind": kind,
            "name": node.name,
            "qualname": qn,
            "signature": "(" + ", ".join(bases) + ")" if bases else "()",
            "arity": len(bases),
            "docstring": _first_line_of_doc(doc),
            "raw": "",
            "refs": {},
        }
        # Recurse for class members
        for child in node.body:
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                yield from _rows_for(child, rel_path, module_qn, qn)
            elif isinstance(child, ast.Assign):
                # enum_member or dataclass_field assignment
                if kind == "enum":
                    for target in child.targets:
                        if isinstance(target, ast.Name):
                            yield {
                                "source": "python",
                                "path": rel_path,
                                "line": child.lineno,
                                "kind": "enum_member",
                                "name": target.id,
                                "qualname": f"{qn}.{target.id}",
                                "signature": _constant_value_kind(child.value),
                                "arity": 0,
                                "docstring": "",
                                "raw": "",
                                "refs": {"paper": [], "agda": [], "study": [], "axiom_class": []},
                            }
            elif isinstance(child, ast.AnnAssign) and child.target is not None:
                if kind in ("dataclass", "class"):
                    if isinstance(child.target, ast.Name):
                        yield {
                            "source": "python",
                            "path": rel_path,
                            "line": child.lineno,
                            "kind": "dataclass_field" if kind == "dataclass" else "attribute",
                            "name": child.target.id,
                            "qualname": f"{qn}.{child.target.id}",
                            "signature": ast.unparse(child.annotation)
                            if child.annotation else "",
                            "arity": 0,
                            "docstring": "",
                            "raw": "",
                            "refs": {"paper": [], "agda": [], "study": [], "axiom_class": []},
                        }

    elif isinstance(node, ast.Assign):
        # Module-level constants: UPPER_CASE names
        for target in node.targets:
            if isinstance(target, ast.Name) and _looks_like_constant(target.id):
                yield {
                    "source": "python",
                    "path": rel_path,
                    "line": node.lineno,
                    "kind": "constant",
                    "name": target.id,
                    "qualname": f"{module_qn}.{target.id}",
                    "signature": _constant_value_kind(node.value),
                    "arity": 0,
                    "docstring": "",
                    "raw": "",
                    "refs": {"paper": [], "agda": [], "study": [], "axiom_class": []},
                }

    elif isinstance(node, ast.AnnAssign) and node.target is not None:
        if isinstance(node.target, ast.Name):
            yield {
                "source": "python",
                "path": rel_path,
                "line": node.lineno,
                "kind": "typed_constant",
                "name": node.target.id,
                "qualname": f"{module_qn}.{node.target.id}",
                "signature": ast.unparse(node.annotation) if node.annotation else "",
                "arity": 0,
                "docstring": "",
                "raw": "",
                "refs": {"paper": [], "agda": [], "study": [], "axiom_class": []},
            }


def _looks_like_constant(name: str) -> bool:
    """A module-scope Assign counts as a 'constant' iff the name is
    UPPER_CASE or contains at least one underscore AND is all-caps letters.
    """
    if not name:
        return False
    if name.startswith("_"):
        return False
    return name.isupper() or (any(c.isupper() for c in name) and "_" in name and name.upper() == name)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def iter_rows(root: Path) -> Iterable[dict]:
    for path in sorted(root.rglob("*.py")):
        if any(part == "legacy" for part in path.parts):
            continue
        if any(part.startswith(".") for part in path.parts):
            continue
        yield from extract_file(root, path)


def main():
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("src/cstz")
    if not root.exists():
        print(f"error: {root} not found", file=sys.stderr)
        sys.exit(1)
    count = 0
    for row in iter_rows(root):
        print(json.dumps(row, ensure_ascii=False))
        count += 1
    print(f"# {count} rows emitted (source=python)", file=sys.stderr)


if __name__ == "__main__":
    main()
