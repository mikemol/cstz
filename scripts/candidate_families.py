"""Candidate discriminator-family generators for κ-evolution.

Per Appendix F's ``CANDIDATE_FORMS`` pattern (``scripts/app_f_trace.py``):
when the calibration loop's residue plateaus under the current
discriminator basis, we try each candidate family generator, register
the new discriminators it produces, re-measure, and keep the family
that most reduces the residue.

Each generator takes the full corpus and emits a list of
``(family_tag, key, weight)`` triples.  The family_tag is unique per
generator; the key identifies the specific discriminator within the
family.  All generators are GRAMMAR-REFLECTED in the sense that they
derive their discriminator set from the corpus (names, tokens, paths,
AST kinds), not from hand-specified patterns.

Generator contract:
    gen(all_decls, paper_rows) -> Iterable[(family_tag, key, weight)]
    fires(decl, family_tag, key) -> bool

The calibration driver registers each ``(family_tag, key, weight)``
as a new discriminator (reusing the ParallelRegistry's one-hot
allocator), then computes each decl's bitmap by walking the corpus
again asking ``fires()`` for every registered discriminator.
"""

from __future__ import annotations

import math
import sys
from collections import Counter
from pathlib import Path
from typing import Callable, Iterable

sys.path.insert(0, str(Path(__file__).parent))

from align_perspectives import normalize_name  # noqa: E402


# ---------------------------------------------------------------------------
# Family generators
# ---------------------------------------------------------------------------


def gen_name_bigrams(all_decls, paper_rows):
    """Bigrams of adjacent tokens in each decl's normalized name.

    Produces one discriminator per corpus-observed bigram.  A decl fires
    on bigram (T1, T2) iff T1 and T2 both appear in its name's token
    set AND some name contains them as adjacent tokens.

    We filter to bigrams that occur in at least 2 decls (signal) and
    fewer than 20% of decls (discriminating).
    """
    bigram_counts: Counter = Counter()
    decl_bigrams: dict[int, set[tuple[str, str]]] = {}

    def _name_bigrams(name: str) -> list[tuple[str, str]]:
        """Return adjacent-token bigrams for a name, after normalization."""
        # Split on non-alphanumeric then normalize each piece
        import re
        raw_parts = re.split(r"[^A-Za-z0-9]+", name)
        parts: list[str] = []
        for p in raw_parts:
            toks = list(normalize_name(p))
            parts.extend(sorted(toks))
        return [(parts[i], parts[i + 1]) for i in range(len(parts) - 1) if parts[i] != parts[i + 1]]

    for idx, d in enumerate(all_decls):
        name_parts = []
        # include last segment emphatically
        if "." in d.name:
            name_parts.append(d.name.split(".")[-1])
        name_parts.append(d.name)
        my_bigrams = set()
        for np_ in name_parts:
            for bg in _name_bigrams(np_):
                my_bigrams.add(bg)
                bigram_counts[bg] += 1
        decl_bigrams[idx] = my_bigrams

    n = len(all_decls)
    max_df = max(int(0.20 * n), 2)
    kept = {bg for bg, c in bigram_counts.items() if 2 <= c <= max_df}
    for bg in kept:
        df = bigram_counts[bg]
        w = math.log(n / df) + 1.0
        yield ("name_bigram", f"{bg[0]}+{bg[1]}", w)


def gen_path_segments(all_decls, paper_rows):
    """Segments of qualified-name paths as discriminators.

    For CSTZ.Axiom.Operationalist: segments are (``CSTZ``, ``Axiom``,
    ``Operationalist``), plus their normalized-name equivalents.
    For python qualnames cstz.axioms.check_operationalist: segments
    include ``cstz``, ``axioms``, ``check_operationalist``.
    For paper labels def:operationalist: segments include ``def``,
    ``operationalist``.

    Segments that appear in many decls across DIFFERENT sources are
    higher-signal bridges between the sources.
    """
    seg_counts: Counter = Counter()
    seg_by_source: dict[str, set[str]] = {}

    for d in all_decls:
        qn = d.qualname
        # Split on both '.' and ':' and '-' and '_'
        import re
        parts = re.split(r"[.:\-_/]+", qn.lower())
        parts = [p for p in parts if p and len(p) >= 3]
        for seg in parts:
            seg_counts[seg] += 1
            seg_by_source.setdefault(seg, set()).add(d.source)

    n = len(all_decls)
    # Keep segments that appear across ≥2 sources and in moderate df range
    for seg, c in seg_counts.items():
        if len(seg_by_source[seg]) < 2:
            continue
        if c > int(0.30 * n):
            continue  # too common
        if c < 2:
            continue
        w = math.log(n / c) + 1.0
        yield ("path_segment", seg, w)


def gen_long_tokens(all_decls, paper_rows):
    """Long (≥7 char) tokens as high-specificity discriminators.

    Tokens of length ≥ 7 that appear in a decl's body/name tokens are
    rare enough to be highly discriminating.  The existing ``token``
    family already covers them but with IDF-weight-only; here we give
    them an extra family-level weight bonus for being long.
    """
    long_token_counts: Counter = Counter()
    for d in all_decls:
        for t in d.tokens:
            if len(t) >= 7:
                long_token_counts[t] += 1
    n = len(all_decls)
    for t, c in long_token_counts.items():
        if c < 2 or c > int(0.15 * n):
            continue
        w = math.log(n / c) + 1.0
        yield ("long_token", t, w * 1.5)  # 1.5× bonus for length


def gen_section_match(all_decls, paper_rows):
    """Paper-section-number discriminator.

    A decl "belongs to" section N if:
      - paper: its section_num == N
      - agda/python: its docstring contains "§N" or "Section N"

    One discriminator per section present in the paper.
    """
    # Derive valid section numbers from paper_rows
    sections = {r.get("section_num") for r in paper_rows if r.get("section_num")}
    n = len(all_decls)
    for s in sorted(sections):
        yield ("section_num", str(s), 1.5)


def gen_kind_pair(all_decls, paper_rows):
    """Kind-pair discriminators: (decl_kind, child_kind) edges, but
    observed across sources.  Different sources have different kind
    names; we keep each source's pairs separate but give them a uniform
    family tag so the feedback loop can reason about "edge" signal
    family-wise.
    """
    pair_counts: Counter = Counter()
    for d in all_decls:
        for field, child_kind in d.child_sig:
            pair_counts[(d.source, d.kind, child_kind)] += 1
    n = len(all_decls)
    for (src, pk, ck), c in pair_counts.items():
        if c < 3 or c > int(0.20 * n):
            continue
        w = math.log(n / c) + 1.0
        yield ("kind_pair", f"{src}/{pk}→{ck}", w)


# ---------------------------------------------------------------------------
# Fire-check functions (per family)
# ---------------------------------------------------------------------------


def fires_name_bigram(decl, key: str) -> bool:
    """Does decl's name contain the bigram (T1, T2) as adjacent tokens?"""
    t1, t2 = key.split("+", 1)
    import re
    raw_parts = re.split(r"[^A-Za-z0-9]+", decl.name)
    for rp in raw_parts:
        toks = sorted(list(normalize_name(rp)))
        for i in range(len(toks) - 1):
            if toks[i] == t1 and toks[i + 1] == t2:
                return True
    return False


def fires_path_segment(decl, key: str) -> bool:
    """Does decl's qualname contain the segment?"""
    import re
    parts = re.split(r"[.:\-_/]+", decl.qualname.lower())
    return key in parts


def fires_long_token(decl, key: str) -> bool:
    """Does decl's token bag contain the long token?"""
    return key in decl.tokens


def fires_section_match(decl, key: str, paper_row_by_qn: dict | None = None, docstring: str = "") -> bool:
    """Does decl belong to section N?

    Paper: decl's section_num == N.
    Agda/Python: docstring contains ``§N`` or ``Section N``.
    """
    s = int(key)
    if decl.source == "paper" and paper_row_by_qn is not None:
        pr = paper_row_by_qn.get(decl.qualname)
        if pr:
            return pr.get("section_num") == s
    if docstring:
        return f"§{s}" in docstring or f"Section {s}" in docstring or f"§ {s}" in docstring
    return False


def fires_kind_pair(decl, key: str) -> bool:
    """Does decl's (source, kind→child_kind) match the key?"""
    expected_src, rest = key.split("/", 1)
    if decl.source != expected_src:
        return False
    pk, ck = rest.split("→", 1)
    if decl.kind != pk:
        return False
    return any(child_kind == ck for _, child_kind in decl.child_sig)


# ---------------------------------------------------------------------------
# Public registry of generators
# ---------------------------------------------------------------------------


FAMILY_GENERATORS: dict[str, Callable] = {
    "name_bigram":   gen_name_bigrams,
    "path_segment":  gen_path_segments,
    "long_token":    gen_long_tokens,
    "section_num":   gen_section_match,
    "kind_pair":     gen_kind_pair,
}


FIRE_FUNCTIONS: dict[str, Callable] = {
    "name_bigram":   fires_name_bigram,
    "path_segment":  fires_path_segment,
    "long_token":    fires_long_token,
    "section_num":   fires_section_match,
    "kind_pair":     fires_kind_pair,
}
