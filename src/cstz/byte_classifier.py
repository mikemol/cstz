"""Bitstream → SPPF classifier.

Factorizes arbitrary byte sequences into a three-fiber SPPF by building
a balanced binary tree over the bytes. Each level doubles the span:
bytes → bigrams → 4-grams → 8-grams → ...

Three fibers:
  σ (syntax)      — byte/n-gram identity (what bytes are here)
  τ (type)        — context identity (what bytes surround this)
  κ (categorical) — structural role (character class, position)

Usage::

    from cstz import factorize_bytes

    sppf = factorize_bytes(b"Hello, World!")
    print(sppf.summary())

    sppf = factorize_bytes("/path/to/file.bin")
    print(sppf.summary())
"""

import math
from pathlib import Path

from .core import SPPF


def factorize_bytes(data, context_width=4, chunk_levels=None):
    """Factorize an arbitrary bitstream into a three-fiber SPPF.

    Parameters
    ----------
    data : bytes, bytearray, or path-like
        The bitstream to factorize. If a path, reads the file.
    context_width : int
        Number of preceding bytes used for τ-context. Default 4.
    chunk_levels : int or None
        How many levels of the binary tree to build. Default: log2(len).

    Returns
    -------
    SPPF
    """
    if isinstance(data, (str, Path)):
        data = Path(data).read_bytes()
    if isinstance(data, memoryview):
        data = bytes(data)

    n = len(data)
    if n == 0:
        return SPPF()

    if chunk_levels is None:
        chunk_levels = min(int(math.log2(max(n, 2))), 20)

    sppf = SPPF()

    # Level 0: individual bytes as leaf nodes.
    prev_tids = []
    prev_sids = []
    prev_kids = []

    for i, b in enumerate(data):
        ast_type = "byte"
        params = (("v", b),)

        ctx_start = max(0, i - context_width)
        dep_type = f"ctx:{data[ctx_start:i].hex()}" if i > 0 else "ctx:^"

        kappa_tag = _classify_byte(b)

        sid, tid, kid, _ = sppf._ingest_node(
            ast_type, params, dep_type, kappa_tag,
            (), (), (),
            i, "<bytes>",
        )
        prev_sids.append(sid)
        prev_tids.append(tid)
        prev_kids.append(kid)

    # Higher levels: pair adjacent nodes bottom-up.
    for level in range(1, chunk_levels + 1):
        if len(prev_tids) < 2:
            break

        next_sids = []
        next_tids = []
        next_kids = []

        span = 1 << level
        for j in range(0, len(prev_tids) - 1, 2):
            pos = j * (1 << (level - 1))
            left_s, right_s = prev_sids[j], prev_sids[j + 1]
            left_t, right_t = prev_tids[j], prev_tids[j + 1]
            left_k, right_k = prev_kids[j], prev_kids[j + 1]

            ast_type = f"span_{span}"
            params = (("pos", pos),)

            dep_type = f"L{level}:{sppf.tau.canonical(left_t)}"

            kappa_tag = _classify_span(pos, span, n, level)

            child_sigmas = (left_s, right_s)
            child_taus = (left_t, right_t)
            child_kappas = (left_k, right_k)

            sid, tid, kid, _ = sppf._ingest_node(
                ast_type, params, dep_type, kappa_tag,
                child_sigmas, child_taus, child_kappas,
                pos, "<bytes>",
            )
            next_sids.append(sid)
            next_tids.append(tid)
            next_kids.append(kid)

        if len(prev_tids) % 2 == 1:
            next_sids.append(prev_sids[-1])
            next_tids.append(prev_tids[-1])
            next_kids.append(prev_kids[-1])

        prev_sids = next_sids
        prev_tids = next_tids
        prev_kids = next_kids

    return sppf


def _classify_byte(b):
    """Classify a byte by its structural role."""
    if b == 0:
        return "null"
    if b == 0x0a:
        return "newline"
    if b == 0x0d:
        return "cr"
    if b == 0x20:
        return "space"
    if b == 0x09:
        return "tab"
    if 0x30 <= b <= 0x39:
        return "digit"
    if 0x41 <= b <= 0x5a:
        return "upper"
    if 0x61 <= b <= 0x7a:
        return "lower"
    if 0x21 <= b <= 0x7e:
        return "punct"
    if b < 0x20:
        return "control"
    if 0x80 <= b <= 0xbf:
        return "utf8.cont"
    if 0xc0 <= b <= 0xdf:
        return "utf8.2"
    if 0xe0 <= b <= 0xef:
        return "utf8.3"
    if 0xf0 <= b <= 0xf7:
        return "utf8.4"
    return "high"


def _classify_span(pos, span, total, level):
    """Classify a span by its structural role."""
    if pos == 0:
        return f"head.{level}"
    if pos + span >= total:
        return f"tail.{level}"
    return f"body.{level}"
