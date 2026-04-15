"""Parameterized discriminator primitives for κ-evolution.

Per user feedback ("You're hardcoding stuff that you should allow the
system to organically discover/derive/evolve"), this module exposes
PARAMETERIZED primitives rather than hand-specified family variants.
Each primitive takes a small integer parameter; the calibration loop
tries each (primitive, parameter) combination and adopts the one that
most reduces residue.

The three primitives cover the parse-tree features we can derive
without picking conventions:

    ngram_name(k)      k-gram sequence of adjacent normalized tokens
                       in the decl's name.  k ∈ {2, 3, 4}.

    substring_qualname(k)
                       k-length character substrings of the full
                       qualname.  k ∈ {3, 4, 5, 6, 7}.

    subtree_shape(d)   ordered tuple of (kind, child_kinds) down to
                       depth d in the decl's AST.  d ∈ {1, 2, 3}.

The calibration loop in calibrate_weights.py iterates every
(primitive, parameter) combination; each becomes a candidate family
with a generated tag like ``ngram_name(k=3)``.  The system discovers
which parameters and primitives actually help the oracle — no
hand-picked "best k" for anything.

Each primitive family's discriminators are corpus-derived: a unique
discriminator is registered for every ngram / substring / shape
observed at least twice in the corpus, with IDF-style weights.
"""

from __future__ import annotations

import hashlib
import math
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Callable, Iterable

sys.path.insert(0, str(Path(__file__).parent))

from align_perspectives import normalize_name  # noqa: E402


# ---------------------------------------------------------------------------
# Primitive 1: n-gram of name tokens
# ---------------------------------------------------------------------------


def _name_tokens(name: str) -> list[str]:
    """Split a name into normalized adjacent tokens, preserving order."""
    raw = re.split(r"[^A-Za-z0-9]+", name)
    parts: list[str] = []
    for r in raw:
        for t in sorted(normalize_name(r)):
            parts.append(t)
    return parts


def _ngrams(seq: list[str], n: int) -> list[tuple[str, ...]]:
    return [tuple(seq[i : i + n]) for i in range(len(seq) - n + 1)]


def gen_ngram_name(k: int, all_decls, paper_rows):
    """k-gram family: every k-gram of adjacent name tokens observed in ≥2 decls."""
    counts: Counter = Counter()
    for d in all_decls:
        seen = set()
        # Include both the last segment and the full name
        name_parts: list[str] = []
        if "." in d.name:
            name_parts.extend(_name_tokens(d.name.split(".")[-1]))
        name_parts.extend(_name_tokens(d.name))
        for ng in _ngrams(name_parts, k):
            if ng not in seen:
                counts[ng] += 1
                seen.add(ng)
    n = len(all_decls)
    max_df = max(int(0.15 * n), 2)
    for ng, c in counts.items():
        if c < 2 or c > max_df:
            continue
        key = "|".join(ng)
        w = math.log(n / c) + 1.0
        yield (key, w)


def fires_ngram_name(k: int):
    """Return a fire-check that tests for a specific k-gram in decl name."""
    def _fires(decl, key: str, docstring: str = "") -> bool:
        target = tuple(key.split("|"))
        if len(target) != k:
            return False
        name_parts: list[str] = []
        if "." in decl.name:
            name_parts.extend(_name_tokens(decl.name.split(".")[-1]))
        name_parts.extend(_name_tokens(decl.name))
        for ng in _ngrams(name_parts, k):
            if ng == target:
                return True
        return False
    return _fires


# ---------------------------------------------------------------------------
# Primitive 2: character substring of qualname
# ---------------------------------------------------------------------------


def gen_substring_qualname(k: int, all_decls, paper_rows):
    """k-length character substring family over qualnames."""
    counts: Counter = Counter()
    for d in all_decls:
        s = d.qualname.lower()
        seen = set()
        for i in range(len(s) - k + 1):
            sub = s[i : i + k]
            # Skip if non-alphanumeric (punctuation-heavy substrings are noise)
            if not sub.replace(":", "").replace(".", "").replace("-", "").replace("_", "").isalnum():
                continue
            if sub in seen:
                continue
            seen.add(sub)
            counts[sub] += 1
    n = len(all_decls)
    max_df = max(int(0.12 * n), 2)
    for sub, c in counts.items():
        if c < 2 or c > max_df:
            continue
        w = math.log(n / c) + 1.0
        yield (sub, w)


def fires_substring_qualname(k: int):
    def _fires(decl, key: str, docstring: str = "") -> bool:
        return key in decl.qualname.lower()
    return _fires


# ---------------------------------------------------------------------------
# Primitive 3: subtree topology hash at fixed depth
# ---------------------------------------------------------------------------


def _topology_hash(decl, depth: int) -> str:
    """Compute a bounded-depth topology hash of a decl's child signature.

    Depth 1 = (kind, sorted(child_kinds))
    Depth 2+ would recurse into children, but we only have one level
    of child_sig available on a Decl.  For depth > 1 we fall back to
    concatenating kind + each edge.
    """
    if not hasattr(decl, "child_sig"):
        return decl.kind
    children = tuple(sorted(ck for _, ck in decl.child_sig))
    if depth <= 1:
        sig = f"{decl.kind}({','.join(children)})"
    else:
        # For depth > 1 we can't recurse with only child_sig, so we
        # approximate by concatenating kind, edge count, and children
        sig = f"{decl.kind}[d={depth}]({','.join(children)})"
    h = hashlib.blake2b(sig.encode("utf-8"), digest_size=6)
    return h.hexdigest()


def gen_subtree_shape(d: int, all_decls, paper_rows):
    """Topology-hash family at depth d."""
    counts: Counter = Counter()
    for decl in all_decls:
        counts[_topology_hash(decl, d)] += 1
    n = len(all_decls)
    max_df = max(int(0.15 * n), 2)
    for h, c in counts.items():
        if c < 2 or c > max_df:
            continue
        w = math.log(n / c) + 1.0
        yield (h, w)


def fires_subtree_shape(d: int):
    def _fires(decl, key: str, docstring: str = "") -> bool:
        return _topology_hash(decl, d) == key
    return _fires


# ---------------------------------------------------------------------------
# Primitive registry: (primitive_name, generator_factory, fire_factory, params)
# ---------------------------------------------------------------------------
#
# The calibration loop iterates every (primitive, parameter) pair:
# it calls ``generator_factory(p)`` to get items for parameter p and
# ``fire_factory(p)`` to get the fire-check.  Family tag on registration
# is ``"{primitive}_p{p}"``.


PRIMITIVES: dict[str, tuple[Callable, Callable, list[int]]] = {
    "ngram_name": (gen_ngram_name, fires_ngram_name, [2, 3, 4]),
    "substring_qualname": (gen_substring_qualname, fires_substring_qualname, [3, 4, 5, 6, 7]),
    "subtree_shape": (gen_subtree_shape, fires_subtree_shape, [1, 2]),
}


def enumerate_candidate_families(
    all_decls: list, paper_rows: list[dict]
) -> Iterable[tuple[str, list[tuple[str, float]], Callable]]:
    """Enumerate every (primitive, parameter) combination as a candidate
    family.  Yields (family_tag, items, fire_check_callable) for each.

    The calibration loop tries each in turn, adopts the one with the
    best residue reduction, and records the discovered parameter.
    """
    for primitive_name, (gen_factory, fire_factory, params) in PRIMITIVES.items():
        for p in params:
            tag = f"{primitive_name}_p{p}"
            items = [(k, w) for (k, w) in gen_factory(p, all_decls, paper_rows)]
            if not items:
                continue
            fire = fire_factory(p)
            yield (tag, items, fire)
