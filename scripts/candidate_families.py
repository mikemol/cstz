"""Candidate discriminator primitives for κ-evolution.

Per user feedback ("Are we introducing new X as aliases of bundle
permutations of existing-X?"), this module now exposes ONE structural
primitive (``subtree_shape``) and a residue-driven wedge-candidate
generator (``enumerate_wedge_candidates``) that builds grade-(k+1)
discriminators from currently-active grade-k bits which co-fire on
residue pairs.

Grade-k wedge = conjunction of k grade-1 discriminators.  The
registry stores each wedge as its own bit with parents recorded;
``fire_bitmap`` sets the wedge bit iff both parents' bits are set.

The enumerate_wedge_candidates function implements the paper's
CD-doubling step (Thm 8.6) as data-driven feature construction:
each plateau of the calibration residue triggers articulation of
the next-higher wedge grade, selectively populated from bit-pairs
that co-fire on the residue (the places where the current basis
can't separate oracle-confirmed pairs from rivals).
"""

from __future__ import annotations

import hashlib
import math
import sys
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Callable, Iterable

sys.path.insert(0, str(Path(__file__).parent))


# ---------------------------------------------------------------------------
# Structural primitive: subtree topology hash at fixed depth
# ---------------------------------------------------------------------------


def _topology_hash(decl, depth: int) -> str:
    """Compute a bounded-depth topology hash of a decl's child signature.

    Depth 1 = kind + sorted multiset of child kinds.
    Depth 2+ approximates by appending the depth parameter to the
    hash input (we only have one level of child_sig on a Decl).
    """
    children = tuple(sorted(ck for _, ck in decl.child_sig))
    if depth <= 1:
        sig = f"{decl.kind}({','.join(children)})"
    else:
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
# Primitive registry: only structural survivor is subtree_shape
# ---------------------------------------------------------------------------


PRIMITIVES: dict[str, tuple[Callable, Callable, list[int]]] = {
    "subtree_shape": (gen_subtree_shape, fires_subtree_shape, [1, 2]),
}


def enumerate_candidate_families(
    all_decls: list, paper_rows: list[dict]
) -> Iterable[tuple[str, list[tuple[str, float]], Callable]]:
    """Enumerate every (primitive, parameter) combination for subtree_shape.

    This is the non-wedge branch of candidate generation.  For the
    wedge branch, see ``enumerate_wedge_candidates``.
    """
    for primitive_name, (gen_factory, fire_factory, params) in PRIMITIVES.items():
        for p in params:
            tag = f"{primitive_name}_p{p}"
            items = [(k, w) for (k, w) in gen_factory(p, all_decls, paper_rows)]
            if not items:
                continue
            fire = fire_factory(p)
            yield (tag, items, fire)


# ---------------------------------------------------------------------------
# Wedge-candidate generator — residue-driven grade-k+1 bundle discovery
# ---------------------------------------------------------------------------


def _set_bits(bm: int) -> list[int]:
    """Return the list of set bit positions in a Python int."""
    out = []
    x = bm
    while x:
        lsb = x & -x
        out.append(lsb.bit_length() - 1)
        x &= x - 1
    return out


def enumerate_wedge_candidates(
    registry,
    bitmaps: dict[str, int],
    residue_pairs: list[tuple[str, str]],
    *,
    min_co_fire: int = 3,
    max_candidates: int = 40,
    grade: int = 2,
) -> Iterable[tuple[str, tuple[int, int], float]]:
    """Propose grade-(k+1) wedges of currently-active discriminators.

    For every pair of bits (i, j) that BOTH fire on at least
    ``min_co_fire`` residue pairs, yield a candidate wedge.  The
    candidates are ranked by co-fire count (descending) and limited
    to ``max_candidates``.

    Each yielded entry is ``(family_tag, (parent_a_bid, parent_b_bid),
    weight)``.  The calibration driver then calls
    ``registry.register_wedge`` with the parent family+key strings
    (looked up from bitmap ids) and re-scores.

    ``residue_pairs`` is a list of (src_qn, target_qn) pairs from the
    citation oracle where the aligner currently ranks ``target_qn``
    worse than rank 1 — the places where the current basis can't
    separate the oracle pair from its rivals.
    """
    co_fire: Counter = Counter()
    n = len(residue_pairs)
    if n == 0:
        return
    for (src_qn, tgt_qn) in residue_pairs:
        bm_src = bitmaps.get(src_qn, 0)
        bm_tgt = bitmaps.get(tgt_qn, 0)
        firing = bm_src & bm_tgt
        ids = _set_bits(firing)
        # Skip if no or too many simultaneous firings (would generate
        # combinatorial blowup without signal)
        if len(ids) < 2 or len(ids) > 24:
            continue
        for i, j in combinations(ids, 2):
            co_fire[(i, j)] += 1

    # Yield top candidates
    emitted = 0
    for (i, j), count in co_fire.most_common():
        if count < min_co_fire:
            break
        # Weight = log(N / co_fire_count) + 1  (rare co-firings are
        # stronger signal; common ones are downweighted)
        w = math.log(max(n, 1) / max(count, 1)) + 1.0
        fam_tag = f"wedge_g{grade}"
        yield (fam_tag, (i, j), w)
        emitted += 1
        if emitted >= max_candidates:
            break
