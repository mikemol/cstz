#!/usr/bin/env python3
"""Shared-packed-parse-forest (SPPF) for the CSTZ alignment design space.

Problem: architectural decisions accumulate across sessions.  Each new
Claude session that tries to carry the full design history in its
working context hits the context limit before it can do any coding.
The principles, corrections, rejected alternatives, and open
questions form a DAG with heavy shared substructure (many decisions
reference the same principles; many rejections cite the same
rationale).  A flat conversation log is O(n²) readable per session.

Solution: SPPF-style organization.  Each node is a small JSONL record
with an id and a parents list; walks are selective subgraph dumps.
A new session can load exactly the slice it needs
(``--type principle``, ``--deps-of decision_xyz``, ``--open-questions``)
instead of paging in the whole history.

Node types:
  principle   — architectural invariants that downstream decisions
                must not violate (e.g. "atoms are gap-preserving")
  decision    — concrete design choices; each references the
                principles it implements or balances
  rejected    — design alternatives that were tried and abandoned,
                with rationale linking back to principles they
                violated
  correction  — a revision that supersedes an earlier node; the
                earlier node stays in the graph for provenance
  question    — open ambiguities that need user clarification before
                downstream decisions can be made
  artifact    — concrete code/data files produced; each references
                the decisions it implements

File layout:
  design/principles.jsonl
  design/decisions.jsonl
  design/rejected.jsonl
  design/corrections.jsonl
  design/questions.jsonl
  design/artifacts.jsonl
  design/INDEX.md          — human-readable catalog

Each JSONL record:
  {
    "id": "p-atoms-gap-preserving",
    "type": "principle",
    "title": "Atoms are gap-preserving",
    "body": "...",
    "parents": ["p-belnap-over-boolean"],
    "status": "active" | "superseded" | "deprecated",
    "superseded_by": null | "c-xyz",
    "session": "2026-04-15",
    "refs": ["paper:Def 9.8", "paper:Rem 3.17"]
  }
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Iterator

DESIGN_DIR = Path(__file__).resolve().parent.parent / "design"
NODE_FILES = {
    "principle":  "principles.jsonl",
    "decision":   "decisions.jsonl",
    "rejected":   "rejected.jsonl",
    "correction": "corrections.jsonl",
    "question":   "questions.jsonl",
    "artifact":   "artifacts.jsonl",
}


# ---------------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------------


def load_all() -> dict[str, dict]:
    """Load every SPPF node keyed by id."""
    out: dict[str, dict] = {}
    for node_type, fname in NODE_FILES.items():
        path = DESIGN_DIR / fname
        if not path.exists():
            continue
        for line in path.open():
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            rec.setdefault("type", node_type)
            if rec["id"] in out:
                raise ValueError(f"duplicate id {rec['id']!r}")
            out[rec["id"]] = rec
    return out


def load_by_type(node_type: str) -> list[dict]:
    path = DESIGN_DIR / NODE_FILES[node_type]
    if not path.exists():
        return []
    return [json.loads(l) for l in path.open() if l.strip()]


# ---------------------------------------------------------------------------
# Walks
# ---------------------------------------------------------------------------


def walk_deps(graph: dict[str, dict], root_id: str) -> list[dict]:
    """Return all transitive parents of ``root_id`` (topologically sorted,
    leaves first).  The returned list is the minimal slice a reader
    needs to fully understand ``root_id``."""
    visited: set[str] = set()
    order: list[dict] = []

    def visit(node_id: str) -> None:
        if node_id in visited:
            return
        visited.add(node_id)
        node = graph.get(node_id)
        if node is None:
            return
        for p in node.get("parents", []):
            visit(p)
        order.append(node)

    visit(root_id)
    return order


def walk_dependents(graph: dict[str, dict], root_id: str) -> list[dict]:
    """Everything that transitively depends ON ``root_id``."""
    children: dict[str, list[str]] = defaultdict(list)
    for nid, n in graph.items():
        for p in n.get("parents", []):
            children[p].append(nid)

    visited: set[str] = set()
    out: list[dict] = []

    def visit(node_id: str) -> None:
        for c in children.get(node_id, []):
            if c in visited:
                continue
            visited.add(c)
            out.append(graph[c])
            visit(c)

    visit(root_id)
    return out


def open_questions(graph: dict[str, dict]) -> list[dict]:
    return [n for n in graph.values()
            if n.get("type") == "question" and n.get("status", "open") == "open"]


def active_principles(graph: dict[str, dict]) -> list[dict]:
    return [n for n in graph.values()
            if n.get("type") == "principle" and n.get("status", "active") == "active"]


# ---------------------------------------------------------------------------
# Writing
# ---------------------------------------------------------------------------


def append_node(node: dict) -> None:
    """Append a single node to its type's JSONL file."""
    if "id" not in node or "type" not in node:
        raise ValueError("node must have id and type")
    fname = NODE_FILES[node["type"]]
    path = DESIGN_DIR / fname
    path.parent.mkdir(parents=True, exist_ok=True)
    # Verify id uniqueness
    existing = load_all()
    if node["id"] in existing:
        raise ValueError(f"id {node['id']!r} already exists")
    with path.open("a") as f:
        f.write(json.dumps(node, ensure_ascii=False) + "\n")


def supersede(old_id: str, new_node: dict) -> None:
    """Mark ``old_id`` as superseded by ``new_node``.  The new node must
    be a correction whose parents include ``old_id``."""
    if new_node.get("type") != "correction":
        raise ValueError("new node must be of type 'correction'")
    if old_id not in new_node.get("parents", []):
        raise ValueError(f"correction must reference {old_id} in parents")
    append_node(new_node)
    # Update the superseded record's status in place
    graph = load_all()
    if old_id not in graph:
        raise ValueError(f"no node {old_id}")
    old = graph[old_id]
    fname = NODE_FILES[old["type"]]
    path = DESIGN_DIR / fname
    rewritten = []
    for line in path.open():
        line = line.strip()
        if not line:
            continue
        rec = json.loads(line)
        if rec["id"] == old_id:
            rec["status"] = "superseded"
            rec["superseded_by"] = new_node["id"]
        rewritten.append(json.dumps(rec, ensure_ascii=False))
    path.write_text("\n".join(rewritten) + "\n")


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def render_node_brief(node: dict) -> str:
    status = node.get("status", "active")
    marker = {
        "active": "●", "open": "?", "superseded": "✗",
        "deprecated": "✗", "closed": "✓",
    }.get(status, " ")
    return f"{marker} [{node['id']}] {node.get('title', '')}"


def render_node_full(node: dict, graph: dict[str, dict]) -> str:
    lines = [
        f"# {node['id']}  ({node['type']})",
        f"Title: {node.get('title', '')}",
        f"Status: {node.get('status', 'active')}",
    ]
    if node.get("superseded_by"):
        lines.append(f"Superseded by: {node['superseded_by']}")
    parents = node.get("parents", [])
    if parents:
        lines.append("Parents:")
        for p in parents:
            pn = graph.get(p)
            if pn:
                lines.append(f"  - {render_node_brief(pn)}")
            else:
                lines.append(f"  - {p} [MISSING]")
    if node.get("refs"):
        lines.append(f"Refs: {', '.join(node['refs'])}")
    lines.append("")
    lines.append(node.get("body", ""))
    return "\n".join(lines)


def render_index() -> str:
    graph = load_all()
    by_type: dict[str, list[dict]] = defaultdict(list)
    for n in graph.values():
        by_type[n.get("type", "unknown")].append(n)

    lines = ["# CSTZ Design SPPF — Index", ""]
    lines.append("Generated by `python scripts/design_sppf.py index`.")
    lines.append("")
    lines.append("Each node is a line in `design/<type>s.jsonl`.")
    lines.append("Use `python scripts/design_sppf.py show <id>` for full detail.")
    lines.append("Use `python scripts/design_sppf.py deps <id>` for a minimal slice.")
    lines.append("")

    for node_type in ("principle", "decision", "rejected", "correction",
                      "question", "artifact"):
        nodes = by_type.get(node_type, [])
        if not nodes:
            continue
        lines.append(f"## {node_type.capitalize()}s ({len(nodes)})")
        lines.append("")
        for n in sorted(nodes, key=lambda x: x["id"]):
            lines.append(f"- {render_node_brief(n)}")
        lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Walk the CSTZ design SPPF.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("index", help="print human-readable catalog").set_defaults(
        action=lambda args: print(render_index())
    )

    p_show = sub.add_parser("show", help="print full detail for a node")
    p_show.add_argument("id")
    p_show.set_defaults(action=_cmd_show)

    p_deps = sub.add_parser("deps", help="minimal transitive-parents slice")
    p_deps.add_argument("id")
    p_deps.set_defaults(action=_cmd_deps)

    p_dep = sub.add_parser("dependents", help="everything depending on id")
    p_dep.add_argument("id")
    p_dep.set_defaults(action=_cmd_dependents)

    sub.add_parser("questions", help="open questions only").set_defaults(
        action=_cmd_questions
    )
    sub.add_parser("principles", help="active principles only").set_defaults(
        action=_cmd_principles
    )

    p_list = sub.add_parser("list", help="list nodes of a given type")
    p_list.add_argument("type", choices=list(NODE_FILES.keys()))
    p_list.set_defaults(action=_cmd_list)

    args = parser.parse_args()
    args.action(args)


def _cmd_show(args) -> None:
    graph = load_all()
    n = graph.get(args.id)
    if n is None:
        print(f"no node {args.id}", file=sys.stderr)
        sys.exit(1)
    print(render_node_full(n, graph))


def _cmd_deps(args) -> None:
    graph = load_all()
    if args.id not in graph:
        print(f"no node {args.id}", file=sys.stderr)
        sys.exit(1)
    for n in walk_deps(graph, args.id):
        print(render_node_brief(n))


def _cmd_dependents(args) -> None:
    graph = load_all()
    if args.id not in graph:
        print(f"no node {args.id}", file=sys.stderr)
        sys.exit(1)
    for n in walk_dependents(graph, args.id):
        print(render_node_brief(n))


def _cmd_questions(args) -> None:
    graph = load_all()
    for n in open_questions(graph):
        print(render_node_brief(n))


def _cmd_principles(args) -> None:
    graph = load_all()
    for n in active_principles(graph):
        print(render_node_brief(n))


def _cmd_list(args) -> None:
    for n in load_by_type(args.type):
        print(render_node_brief(n))


if __name__ == "__main__":
    main()
