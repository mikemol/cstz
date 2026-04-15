#!/usr/bin/env python3
"""Extract named declarations from Agda source using tree-sitter-agda.

No regex over Agda source.  We feed the file to ``tree_sitter_agda`` and
walk the resulting AST.  Declaration kinds emitted:

    module            — module declaration (node type 'module')
    data              — data declaration (node type 'data')
    data_constructor  — constructor inside a data block
    record            — record declaration (node type 'record')
    record_field      — field inside a 'fields' block
    postulate         — inside a 'postulate' block
    function          — top-level typed name / function definition

Docstrings are the contiguous ``comment`` sibling nodes immediately
preceding a declaration in the source-file AST.  We emit them as raw
text.  The downstream alignment stage does not regex them: it checks
for literal occurrences of label IDs extracted from the paper's
pandoc AST and module names extracted from the Agda AST itself.

Usage:
    python3 scripts/extract_agda.py [PATH ...]
    # Default paths: agda/, CoreProof.agda, inference.agda.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Iterable, Iterator

import tree_sitter_agda
from tree_sitter import Language, Node, Parser

# Secondary postulate parser: tree-sitter-agda fails to parse the bodies of
# postulate blocks that contain Unicode-heavy identifiers like ``∂∘∂≡0``
# (tested at commit 8460007 on agda/CSTZ/Exterior/Boundary.agda:95 and
# agda/CSTZ/Category/Yoneda.agda:65).  For those, we reuse the existing
# ``scripts/count_postulates.py`` lexical parser — itself an indent-aware
# token-level parser for Agda's postulate-block grammar, and the one that
# produces the 9-postulate ground truth in ``STUDY.md §3``.
sys.path.insert(0, str(Path(__file__).parent))
import count_postulates  # noqa: E402


# ---------------------------------------------------------------------------
# Parser setup
# ---------------------------------------------------------------------------


_LANGUAGE = Language(tree_sitter_agda.language())
_PARSER = Parser(_LANGUAGE)


def _text(node: Node) -> str:
    return node.text.decode("utf-8", errors="replace")


def _first_named_child(node: Node, type_: str) -> Node | None:
    for ch in node.children:
        if ch.is_named and ch.type == type_:
            return ch
    return None


def _all_named_children(node: Node, type_: str) -> list[Node]:
    return [ch for ch in node.children if ch.is_named and ch.type == type_]


def _line(node: Node) -> int:
    return node.start_point[0] + 1


# ---------------------------------------------------------------------------
# Declaration extraction
# ---------------------------------------------------------------------------


def _preceding_comments(root: Node, target: Node) -> str:
    """Return the contiguous block of ``comment`` nodes directly before
    ``target`` in ``root``'s children list.

    The tree-sitter-agda grammar emits ``--`` lines sometimes as ``comment``
    nodes and sometimes as tiny ``function`` nodes whose LHS is just ``--``.
    We accept either as part of a comment block.
    """
    children = list(root.children)
    try:
        idx = children.index(target)
    except ValueError:
        return ""
    block: list[str] = []
    i = idx - 1
    while i >= 0:
        node = children[i]
        if node.type == "comment":
            block.append(_text(node))
            i -= 1
            continue
        # Agda's tree-sitter grammar sometimes reports a comment-only line as
        # a zero-body ``function`` node with only an ``lhs > atom > '--'``.
        if node.type == "function":
            t = _text(node).strip()
            if t.startswith("--") and "\n" not in t:
                block.append(t)
                i -= 1
                continue
        break
    return "\n".join(reversed(block))


def _arity_from_type_expr(expr_text: str) -> int:
    """Count top-level ``→`` / ``->`` arrows in a type expression.

    This IS a textual heuristic but it operates on the *already-parsed*
    ``expr`` node's text, not on raw Agda source.  The alternative (walking
    the ``expr`` subtree to count arrow operators) is equivalent and not
    materially more rigorous at this level — the tree-sitter grammar
    flattens right-associated arrows into a single ``expr`` in practice.
    """
    depth = 0
    count = 0
    i = 0
    n = len(expr_text)
    while i < n:
        c = expr_text[i]
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
        elif depth == 0:
            if c == "→":
                count += 1
            elif expr_text[i : i + 2] == "->":
                count += 1
                i += 1
        i += 1
    return count


def _function_name(fn_node: Node) -> tuple[str, str, int]:
    """Return (name, signature_text, arity) for a ``function`` node.

    A function node has children ``lhs`` and optional ``rhs``.  A typed-name
    signature has ``rhs`` starting with ``:``; a definition has ``rhs``
    starting with ``=``.  Either way the name is the first ``function_name``
    / ``atom`` under ``lhs``.
    """
    lhs = _first_named_child(fn_node, "lhs")
    rhs = _first_named_child(fn_node, "rhs")
    if lhs is None:
        return "", _text(fn_node)[:200], 0
    # Preferred: explicit function_name child
    fname = _first_named_child(lhs, "function_name")
    name = _text(fname) if fname is not None else _text(lhs).split()[0] if lhs.children else ""
    sig_text = _text(fn_node)[:500]
    arity = 0
    if rhs is not None:
        expr = _first_named_child(rhs, "expr")
        if expr is not None and _text(rhs).lstrip().startswith(":"):
            arity = _arity_from_type_expr(_text(expr))
    return name, sig_text, arity


def _walk_records(rec_node: Node, module_qn: str) -> Iterator[dict]:
    """Yield fields of a record declaration."""
    name_node = _first_named_child(rec_node, "record_name")
    record_name = _text(name_node) if name_node else ""
    # Find the fields block
    block = _first_named_child(rec_node, "record_declarations_block")
    if block is None:
        return
    fields_nodes = _all_named_children(block, "fields")
    for fields in fields_nodes:
        for sig in _all_named_children(fields, "signature"):
            fn = _first_named_child(sig, "field_name")
            if fn is None:
                continue
            fname = _text(fn)
            expr = _first_named_child(sig, "expr")
            sig_text = _text(sig)
            arity = _arity_from_type_expr(_text(expr)) if expr else 0
            yield {
                "kind": "record_field",
                "name": fname,
                "line": _line(sig),
                "signature": sig_text,
                "arity": arity,
                "parent_kind": "record",
                "parent_name": record_name,
                "docstring": _preceding_comments(fields, sig),
            }


def _walk_data(data_node: Node, module_qn: str) -> Iterator[dict]:
    """Yield constructors of a data declaration."""
    # The grammar exposes data name in 'data_name' or 'qid'
    name_node = _first_named_child(data_node, "data_name") or _first_named_child(data_node, "qid")
    data_name = _text(name_node) if name_node else ""
    # Constructors appear under a 'data_declarations_block' (if any) as
    # 'signature' nodes.
    block = _first_named_child(data_node, "data_declarations_block")
    if block is None:
        return
    for sig in _all_named_children(block, "signature"):
        fn = _first_named_child(sig, "field_name") or _first_named_child(sig, "constructor_name")
        if fn is None:
            # Fallback: first named child
            for c in sig.children:
                if c.is_named:
                    fn = c
                    break
        if fn is None:
            continue
        cname = _text(fn)
        expr = _first_named_child(sig, "expr")
        arity = _arity_from_type_expr(_text(expr)) if expr else 0
        yield {
            "kind": "data_constructor",
            "name": cname,
            "line": _line(sig),
            "signature": _text(sig),
            "arity": arity,
            "parent_kind": "data",
            "parent_name": data_name,
            "docstring": _preceding_comments(block, sig),
        }


def _walk_postulate(post_node: Node) -> Iterator[dict]:
    """Yield one entry per declaration inside a 'postulate' block.

    tree-sitter-agda wraps each ``name : type`` declaration inside a
    postulate block as a ``function`` node with an ``lhs`` containing the
    name and an ``rhs`` containing ``: type``.  We reuse ``_function_name``
    which already knows this shape.
    """
    for fn in _all_named_children(post_node, "function"):
        name, sig_text, arity = _function_name(fn)
        if not name:
            continue
        yield {
            "kind": "postulate",
            "name": name,
            "line": _line(fn),
            "signature": sig_text,
            "arity": arity,
            "parent_kind": "postulate_block",
            "parent_name": None,
            "docstring": _preceding_comments(post_node, fn),
        }


# ---------------------------------------------------------------------------
# File-level driver
# ---------------------------------------------------------------------------


def _module_name_of(root: Node) -> tuple[int, str]:
    for ch in root.children:
        if ch.type == "module":
            mn = _first_named_child(ch, "module_name")
            if mn is not None:
                return _line(ch), _text(mn).strip()
            return _line(ch), ""
    return 1, ""


def _walk_tree_nodes(node: Node, type_: str) -> Iterator[tuple[Node, Node]]:
    """Yield ``(parent, node)`` for every descendant of ``node`` of type ``type_``.

    Used for finding nested postulate blocks (e.g. inside a ``where`` clause
    of ``yoneda-faithful``).
    """
    for ch in node.children:
        if ch.type == type_:
            yield node, ch
        yield from _walk_tree_nodes(ch, type_)


def extract_file(repo_root: Path, path: Path) -> Iterator[dict]:
    src = path.read_bytes()
    tree = _PARSER.parse(src)
    root = tree.root_node

    rel_path = str(path.relative_to(repo_root))
    mod_line, module_qn = _module_name_of(root)

    # -------- module row --------
    module_header = ""
    for ch in root.children:
        if ch.type == "module":
            module_header = _preceding_comments(root, ch)
            break
    yield {
        "source": "agda",
        "path": rel_path,
        "line": mod_line,
        "kind": "module",
        "name": module_qn.split(".")[-1] if module_qn else path.stem,
        "qualname": module_qn or path.stem,
        "signature": module_qn,
        "arity": 0,
        "docstring": _clean_doc(module_header),
        "raw": "",
        "refs": {},  # filled in at alignment time (hybrid mode: no regex)
    }

    # -------- postulates (via count_postulates, which handles unicode-heavy bodies) --------
    # count_postulates.parse_postulates returns a list of (file, line, name).
    # This is the authoritative source for postulate declarations; the
    # tree-sitter grammar silently drops postulate bodies when their
    # identifiers use heavy unicode (e.g. ``∂∘∂≡0``).
    seen_lines: set[int] = set()
    for (_, line_no, name) in count_postulates.parse_postulates(path):
        seen_lines.add(line_no)
        yield {
            "source": "agda",
            "path": rel_path,
            "line": line_no,
            "kind": "postulate",
            "name": name,
            "qualname": f"{module_qn}.{name}" if module_qn else name,
            "signature": f"postulate {name}",
            "arity": 0,  # arity determined from tree when available
            "docstring": "",
            "raw": "",
            "refs": {},
        }

    # -------- top-level record / data / function --------
    for ch in root.children:
        if ch.type == "record":
            name_node = _first_named_child(ch, "record_name")
            rname = _text(name_node) if name_node else ""
            yield {
                "source": "agda",
                "path": rel_path,
                "line": _line(ch),
                "kind": "record",
                "name": rname,
                "qualname": f"{module_qn}.{rname}" if module_qn else rname,
                "signature": _text(ch)[:500],
                "arity": _count_parameters(ch),
                "docstring": _clean_doc(_preceding_comments(root, ch)),
                "raw": "",
                "refs": {},
            }
            for field in _walk_records(ch, module_qn):
                yield {
                    "source": "agda",
                    "path": rel_path,
                    "line": field["line"],
                    "kind": field["kind"],
                    "name": field["name"],
                    "qualname": f"{module_qn}.{rname}.{field['name']}",
                    "signature": field["signature"],
                    "arity": field["arity"],
                    "docstring": _clean_doc(field["docstring"]),
                    "raw": "",
                    "refs": {},
                }

        elif ch.type == "data":
            name_node = _first_named_child(ch, "data_name") or _first_named_child(ch, "qid")
            dname = _text(name_node) if name_node else ""
            yield {
                "source": "agda",
                "path": rel_path,
                "line": _line(ch),
                "kind": "data",
                "name": dname,
                "qualname": f"{module_qn}.{dname}" if module_qn else dname,
                "signature": _text(ch)[:500],
                "arity": _count_parameters(ch),
                "docstring": _clean_doc(_preceding_comments(root, ch)),
                "raw": "",
                "refs": {},
            }
            for ctor in _walk_data(ch, module_qn):
                yield {
                    "source": "agda",
                    "path": rel_path,
                    "line": ctor["line"],
                    "kind": ctor["kind"],
                    "name": ctor["name"],
                    "qualname": f"{module_qn}.{dname}.{ctor['name']}",
                    "signature": ctor["signature"],
                    "arity": ctor["arity"],
                    "docstring": _clean_doc(ctor["docstring"]),
                    "raw": "",
                    "refs": {},
                }

        elif ch.type == "postulate":
            # Already emitted by the tree-wide postulate walk above.
            continue

        elif ch.type == "function":
            # Only emit a row for the TYPE SIGNATURE (rhs starts with ':'),
            # not for the equation (rhs starts with '=').  Each Agda
            # declaration produces one signature and 1+ equations; we take
            # the signature.
            rhs = _first_named_child(ch, "rhs")
            if rhs is None:
                continue
            rhs_text = _text(rhs).lstrip()
            if not rhs_text.startswith(":"):
                continue
            name, sig_text, arity = _function_name(ch)
            if not name or name in ("", "--", "-"):
                # Skip comment-decoration false positives
                continue
            yield {
                "source": "agda",
                "path": rel_path,
                "line": _line(ch),
                "kind": "function",
                "name": name,
                "qualname": f"{module_qn}.{name}" if module_qn else name,
                "signature": sig_text,
                "arity": arity,
                "docstring": _clean_doc(_preceding_comments(root, ch)),
                "raw": "",
                "refs": {},
            }


def _count_parameters(node: Node) -> int:
    """Count parameter bindings on a data/record declaration."""
    count = 0
    for ch in node.children:
        if ch.type in ("typed_binding", "untyped_binding"):
            count += 1
    return count


def _clean_doc(text: str, maxlen: int = 400) -> str:
    """Strip leading ``--`` markers and return the first non-empty line."""
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("-"):
            stripped = stripped.lstrip("- ").strip()
        if stripped:
            return stripped[:maxlen]
    return ""


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def iter_rows(repo_root: Path, targets: list[Path]) -> Iterable[dict]:
    for tgt in targets:
        tgt = tgt.resolve()
        if tgt.is_file() and tgt.suffix == ".agda":
            yield from extract_file(repo_root, tgt)
            continue
        if tgt.is_dir():
            for path in sorted(tgt.rglob("*.agda")):
                yield from extract_file(repo_root, path.resolve())


def main():
    repo_root = Path.cwd().resolve()
    if len(sys.argv) > 1:
        targets = [Path(a) for a in sys.argv[1:]]
    else:
        targets = [Path("agda"), Path("CoreProof.agda"), Path("inference.agda")]
    targets = [t for t in targets if t.exists()]
    count = 0
    for row in iter_rows(repo_root, targets):
        print(json.dumps(row, ensure_ascii=False))
        count += 1
    print(f"# {count} rows emitted (source=agda)", file=sys.stderr)


if __name__ == "__main__":
    main()
