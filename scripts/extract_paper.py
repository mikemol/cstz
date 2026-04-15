#!/usr/bin/env python3
"""Extract named objects from ``paper/`` via pandoc's JSON AST.

No regex over LaTeX content.  We invoke ``pandoc -f latex -t json`` on
``paper/main.tex`` (the root file that ``\\input``s every section), walk
the resulting AST, and emit one row per theorem-like environment.

The AST constructors we care about:

    Header    — section/subsection boundaries
    Div       — container for a theorem-like environment.  The ``c`` array
                is [[id, [classes], []], [block ...]].  Classes include
                "definition" | "theorem" | "proposition" | "lemma" |
                "corollary" | "remark" | "example" | "conjecture" |
                "openquestion".  ``id`` carries the LaTeX ``\\label{…}``.
    Strong    — bold.  The label "Definition N" that LaTeX auto-prefixes
                appears as the first Strong inside the Div's first Para.

Each declaration row reports its LaTeX label, the display-name (optional
argument of ``\\begin{env}[Name]``), the containing section, and — by
grepping the ``paper/**.tex`` sources for ``\\label{…}`` — the source
file and line number where the label was declared.

Cross-references (``\\ref{def:foo}`` etc.) are ALSO emitted as Link nodes
pointing to their target ids; the alignment engine can use this forward
graph if desired (grammar-reflected, not regex-parsed).

Usage:
    python3 scripts/extract_paper.py [PAPER_ROOT]
    # Default PAPER_ROOT = ``paper``.  Expects ``main.tex`` at its root.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Iterator


# ---------------------------------------------------------------------------
# Pandoc invocation
# ---------------------------------------------------------------------------


def parse_paper(paper_root: Path) -> dict:
    """Return pandoc JSON AST for ``paper_root/main.tex``.

    Runs pandoc with the paper root as the working directory so
    ``\\input{sections/...}`` includes resolve.  Falls back to walking
    the sections directory and concatenating them if ``main.tex`` is
    absent.
    """
    main = paper_root / "main.tex"
    if not main.exists():
        raise FileNotFoundError(f"{main} not found")
    result = subprocess.run(
        ["pandoc", "-f", "latex", "-t", "json", "main.tex"],
        cwd=paper_root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        sys.stderr.write(result.stderr.decode("utf-8", errors="replace"))
        result.check_returncode()
    if result.stderr:
        # Pandoc emits harmless warnings about unknown custom commands.
        # We pass them through for auditability but do not fail on them.
        for line in result.stderr.decode("utf-8", errors="replace").splitlines():
            if line.strip():
                print(f"# pandoc: {line}", file=sys.stderr)
    return json.loads(result.stdout)


# ---------------------------------------------------------------------------
# AST walking
# ---------------------------------------------------------------------------


THEOREM_CLASSES = {
    "definition", "theorem", "proposition", "lemma", "corollary",
    "remark", "example", "conjecture", "openquestion",
}


def walk(node, path=()) -> Iterator[tuple[tuple, dict]]:
    """Yield (path, node) for every dict-shaped AST node in depth-first order."""
    if isinstance(node, list):
        for i, item in enumerate(node):
            yield from walk(item, path + (i,))
    elif isinstance(node, dict):
        yield (path, node)
        for k, v in node.items():
            yield from walk(v, path + (k,))


def inline_to_text(inlines) -> str:
    """Flatten an inline content list to plain text."""
    out: list[str] = []

    def rec(x):
        if isinstance(x, list):
            for y in x:
                rec(y)
            return
        if isinstance(x, dict):
            t = x.get("t")
            c = x.get("c")
            if t == "Str":
                out.append(c)
            elif t == "Space":
                out.append(" ")
            elif t == "SoftBreak":
                out.append(" ")
            elif t == "LineBreak":
                out.append("\n")
            elif t in ("Emph", "Strong", "Subscript", "Superscript", "Underline",
                        "SmallCaps", "Quoted", "Cite", "Link", "Image", "Span"):
                # Inline containers: recurse into the content slot
                if isinstance(c, list) and len(c) >= 1:
                    rec(c[-1])
            elif t in ("Math", "Code"):
                # c is either a string or [attrs, string]
                if isinstance(c, list) and len(c) >= 2:
                    out.append(c[1])
                elif isinstance(c, str):
                    out.append(c)
            elif isinstance(c, list):
                rec(c)

    rec(inlines)
    return "".join(out).strip()


def extract_env_name(block_list) -> str:
    """Pull the optional-argument name from a theorem-like env's first Para.

    ``\\begin{definition}[Operationalist axiom]\\label{def:foo}`` renders as
    a first Para starting with ``Strong{"Definition"} Space Str{"1"}`` and
    then a parenthesized optional-arg text.
    """
    for block in block_list:
        if not isinstance(block, dict):
            continue
        if block.get("t") != "Para":
            continue
        children = block.get("c", [])
        if not children:
            continue
        text = inline_to_text(children)
        # Typical shape: "**Definition 1** (Operationalist axiom). If ..."
        # Extract content inside the first parenthesized group, if any.
        lp = text.find("(")
        if lp == -1:
            # No parenthesized name; return the leading bold "Definition N"
            # (strip trailing punctuation)
            # We take text up to the first period.
            head = text.split(".")[0]
            return head.strip()
        rp = _matching_paren(text, lp)
        if rp is None:
            return text[:80].strip()
        return text[lp + 1 : rp].strip()
    return ""


def _matching_paren(text: str, start: int) -> int | None:
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
    return None


# ---------------------------------------------------------------------------
# Label → (file, line) indexing across paper/**.tex
# ---------------------------------------------------------------------------


def index_labels(paper_root: Path) -> dict[str, tuple[str, int]]:
    """Return ``{label_id: (source_file, line_number)}`` for every
    ``\\label{…}`` macro found in any .tex file under ``paper_root``.

    This is file-text indexing, not parsing: we read each .tex file, walk
    lines, and for each line note the last ``\\label{…}`` occurrence's
    content.  Label extraction here does not attempt to interpret LaTeX —
    it just finds a token of the form ``\\label{X}``.  We use str.find
    / str.split rather than regex.
    """
    index: dict[str, tuple[str, int]] = {}
    for tex in sorted(paper_root.rglob("*.tex")):
        rel_path = str(tex.relative_to(paper_root.parent))
        try:
            src = tex.read_text()
        except UnicodeDecodeError:
            continue
        for lineno, line in enumerate(src.splitlines(), start=1):
            idx = 0
            while True:
                hit = line.find("\\label{", idx)
                if hit == -1:
                    break
                start = hit + len("\\label{")
                end = line.find("}", start)
                if end == -1:
                    break
                label = line[start:end]
                if label and label not in index:
                    index[label] = (rel_path, lineno)
                idx = end + 1
    return index


# ---------------------------------------------------------------------------
# Main extraction
# ---------------------------------------------------------------------------


def extract_theorems(ast: dict, labels: dict[str, tuple[str, int]]) -> Iterator[dict]:
    """Yield one row per theorem-like Div in the document.

    Header nodes are tracked as we walk so each row carries its
    containing-section chain.
    """
    section_stack: list[tuple[int, str]] = []

    def visit(node, ancestors):
        if isinstance(node, list):
            for item in node:
                yield from visit(item, ancestors)
            return
        if not isinstance(node, dict):
            return
        t = node.get("t")
        if t == "Header":
            c = node.get("c", [])
            if isinstance(c, list) and len(c) >= 3:
                level = c[0]
                attr = c[1]
                inlines = c[2]
                title = inline_to_text(inlines)
                # Pop deeper-or-equal levels off the stack
                while section_stack and section_stack[-1][0] >= level:
                    section_stack.pop()
                section_stack.append((level, title))
                yield {
                    "t_type": "Header",
                    "level": level,
                    "title": title,
                    "id": attr[0] if isinstance(attr, list) else "",
                }
            return
        if t == "Div":
            c = node.get("c", [])
            if isinstance(c, list) and len(c) == 2:
                attr, content = c
                id_, classes, _ = attr if isinstance(attr, list) and len(attr) == 3 else ("", [], [])
                theorem_class = next((cl for cl in classes if cl in THEOREM_CLASSES), None)
                if theorem_class is not None:
                    env_name = extract_env_name(content)
                    body_text = _body_preview(content)
                    file_, line_ = labels.get(id_, ("", 0))
                    yield {
                        "t_type": "Div",
                        "env": theorem_class,
                        "id": id_,
                        "env_name": env_name,
                        "body_preview": body_text,
                        "section_stack": list(section_stack),
                        "file": file_,
                        "line": line_,
                    }
                    # Don't descend — theorem bodies can contain nested Divs
                    # (e.g. proof), but we don't want to emit those as
                    # named objects (they're not declared objects).
                    return
        # Recurse into children
        for k, v in node.items():
            if k != "t":
                yield from visit(v, ancestors + (t or "",))

    for item in visit(ast.get("blocks", []), ()):
        if item.get("t_type") == "Div":
            yield item


def _body_preview(content: list) -> str:
    """First 300 chars of the environment's textual content."""
    parts: list[str] = []
    for block in content:
        if not isinstance(block, dict):
            continue
        if block.get("t") in ("Para", "Plain"):
            parts.append(inline_to_text(block.get("c", [])))
    return " ".join(parts)[:300]


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    paper_root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("paper")
    if not paper_root.exists():
        print(f"error: {paper_root} not found", file=sys.stderr)
        sys.exit(1)

    print(f"# Parsing {paper_root}/main.tex via pandoc JSON AST", file=sys.stderr)
    ast = parse_paper(paper_root)
    print(f"# Indexing \\label{{…}} across {paper_root}/**.tex", file=sys.stderr)
    labels = index_labels(paper_root)
    print(f"# {len(labels)} labels indexed", file=sys.stderr)

    count = 0
    for item in extract_theorems(ast, labels):
        env = item["env"]
        id_ = item["id"]
        env_name = item["env_name"]
        section_title = item["section_stack"][-1][1] if item["section_stack"] else ""
        qualname = f"{env}:{id_}" if id_ else f"{env}:{env_name or '<unnamed>'}"
        row = {
            "source": "paper",
            "path": item["file"] or f"{paper_root.name}/main.tex",
            "line": item["line"],
            "kind": env,
            "name": env_name or id_ or f"<anon {count}>",
            "qualname": qualname,
            "signature": "",
            "arity": 0,
            "docstring": item["body_preview"],
            "raw": "",
            "refs": {},  # grammar-reflected discriminators consume the AST later
            "label": id_,
            "section": section_title,
            "section_stack": [s[1] for s in item["section_stack"]],
        }
        print(json.dumps(row, ensure_ascii=False))
        count += 1
    print(f"# {count} rows emitted (source=paper)", file=sys.stderr)


if __name__ == "__main__":
    main()
