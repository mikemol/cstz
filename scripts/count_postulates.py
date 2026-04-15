#!/usr/bin/env python3
"""Mechanically count postulate declarations in Agda source.

For each .agda file:
  1. Strip (nestable) block comments  {- ... -}
  2. Strip line comments              --  (followed by space or EOL)
  3. Build a list of (lineno, indent, content) for non-blank lines
  4. Walk the list:
     - On 'postulate' followed by content on the same line, emit one decl.
     - On 'postulate' alone, collect all following lines at a strictly
       greater indent than the 'postulate' line. Within that block, the
       first distinct indent level is the 'declaration indent'; each line
       at *that* indent starts a new declaration. Deeper-indented lines
       are continuation of the previous declaration.

The output is a list of (file, line, name) triples and a total.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


def strip_block_comments(src: str) -> str:
    out = []
    i, depth = 0, 0
    n = len(src)
    while i < n:
        two = src[i:i + 2]
        if two == '{-':
            depth += 1
            i += 2
        elif two == '-}' and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(src[i])
            i += 1
        else:
            # inside a block comment: keep newlines so line numbers stay aligned
            if src[i] == '\n':
                out.append('\n')
            i += 1
    return ''.join(out)


# A line comment starts at '--' that is either at start-of-line or after
# whitespace, and is followed by whitespace, EOL, or a non-symbol character.
# We use the simple rule: '--' preceded by start-of-line or whitespace,
# followed by whitespace or end-of-line.
LINE_COMMENT_RE = re.compile(r'(?:^|(?<=\s))--(?=\s|$)')


def strip_line_comment(line: str) -> str:
    m = LINE_COMMENT_RE.search(line)
    if m:
        return line[:m.start()]
    return line


def logical_lines(src: str):
    src = strip_block_comments(src)
    for lineno, raw in enumerate(src.splitlines(), start=1):
        stripped = strip_line_comment(raw).rstrip()
        if not stripped.strip():
            continue
        indent = len(stripped) - len(stripped.lstrip())
        yield (lineno, indent, stripped.strip())


POSTULATE_RE = re.compile(r'^postulate(?:\s+(.*))?$')


def decl_name(content: str) -> str:
    # Take the identifier(s) before the first ':' that is not part of an
    # operator like '::'.  Agda declarations are 'name : type' or
    # 'name1 name2 ... : type' (mutual).  Return everything before the ':'.
    # Strip backticks or parens if present.
    m = re.match(r'^([^:]*?)\s*:', content)
    if m:
        return m.group(1).strip()
    return content.split()[0]


def parse_postulates(path: Path):
    src = path.read_text()
    lines = list(logical_lines(src))
    decls: list[tuple[str, int, str]] = []
    i = 0
    while i < len(lines):
        lineno, indent, content = lines[i]
        m = POSTULATE_RE.match(content)
        if not m:
            i += 1
            continue
        rest = m.group(1)
        if rest and rest.strip():
            # Inline: 'postulate <decl>'
            decls.append((str(path), lineno, decl_name(rest.strip())))
            i += 1
            continue
        # Block form: collect following lines at indent > indent
        j = i + 1
        block_indent = None
        while j < len(lines):
            ln2, ind2, con2 = lines[j]
            if ind2 <= indent:
                break
            if block_indent is None:
                block_indent = ind2
            if ind2 == block_indent:
                decls.append((str(path), ln2, decl_name(con2)))
            j += 1
        i = j
    return decls


def main():
    root = Path(sys.argv[1] if len(sys.argv) > 1 else '/home/user/cstz/agda/CSTZ')
    files = sorted(root.rglob('*.agda'))
    total = 0
    for f in files:
        for path, lineno, name in parse_postulates(f):
            rel = path.replace('/home/user/cstz/', '')
            print(f'{rel}:{lineno}\t{name}')
            total += 1
    print(f'---\nTotal postulate declarations: {total}')
    print(f'Files scanned: {len(files)}')


if __name__ == '__main__':
    main()
