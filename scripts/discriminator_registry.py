"""Parallel discriminator registry — hundreds of predicates, one score.

Per user framing ("you should have hundreds of discriminators by this point
which aggregate to provide signal in parallel"): rather than running 4
scalar-collapsing passes and combining with hand-tuned weights, we build
ONE discriminator registry where each token / grammar-kind / adjacency
edge / citation-form is its OWN binary predicate, and the alignment score
for a pair (agda, paper) is just the popcount of ``bitmap[agda] &
bitmap[paper]`` weighted by IDF.

This mirrors ``src/cstz/classify/registry.py::DiscriminatorRegistry``
exactly: each discriminator gets a stable one-hot bit-ID in registration
order, and each object's τ-profile is the bitmask of "which of my
discriminators fired".

Discriminator families:

  token/T        — for every corpus token T, fires if T is in the decl's
                   normalized token bag.  Weight = IDF(T).

  kind/SRC/K     — for every (source, grammar-kind) pair, fires if a
                   descendant of the decl has that kind.  Weight = rarity.

  edge/SRC/(P,C) — for every (source, parent_kind, child_kind) adjacency,
                   fires if the decl's subtree contains that edge.
                   Weight = rarity.

  cite/CITE_ID   — for every paper decl's numeric citation (``Def 1.1``,
                   ``Thm 9.20``), fires if CITE_ID appears literally in
                   the decl's docstring.  Weight = 2.0 (high signal).

  name_tok/T     — as ``token`` but restricted to the decl's name, not
                   its body.  Weight = 3.0 (highest signal).

Each decl's bitmask is computed ONCE; pair scoring is a bitwise AND
followed by weighted popcount.  Registry size is bounded by corpus
vocabulary (~2000 hi-IDF tokens) + grammar kinds (~150) + edges (~500)
+ citations (~200) + name-tokens (~1500) ≈ 4400 discriminators.
"""

from __future__ import annotations

import math
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Iterable


@dataclass(frozen=True)
class Discriminator:
    """A single binary predicate on decls with a stable one-hot ID."""
    id: int          # 0-based integer; bit = 1 << id
    family: str      # "token" | "kind" | "edge" | "cite" | "name_tok"
    key: str         # the specific token / kind / edge / citation
    weight: float


class ParallelRegistry:
    """Collects hundreds of discriminators into one bitmap-addressable pool.

    The registry is derived from the CORPUS — tokens, kinds, edges, and
    citation forms observed in the three sources.  No discriminator is
    hand-specified.  ``fire_bitmap(decl)`` returns a single int whose set
    bits are the discriminators that fire on this decl.  Alignment
    between two decls is then ``weighted_popcount(bm_a & bm_b)``.
    """

    def __init__(self) -> None:
        self._by_id: list[Discriminator] = []
        self._by_key: dict[tuple[str, str], int] = {}

    def _register(self, family: str, key: str, weight: float) -> int:
        k = (family, key)
        if k in self._by_key:
            return self._by_key[k]
        did = len(self._by_id)
        self._by_id.append(Discriminator(id=did, family=family, key=key, weight=weight))
        self._by_key[k] = did
        return did

    def register_tokens(self, decls: list, top_n_by_idf: int = 2000) -> None:
        """Register a discriminator for each of the top-N IDF tokens
        appearing in any decl's normalized token bag."""
        df: Counter = Counter()
        for d in decls:
            for t in d.tokens:
                df[t] += 1
        n = len(decls)
        # IDF weight = log(N/df) + 1; rank tokens by IDF descending
        ranked = sorted(df.items(), key=lambda kv: -math.log((n / kv[1]) + 1.0))
        for t, c in ranked[:top_n_by_idf]:
            idf = math.log((n / c) + 1.0)
            self._register("token", t, weight=idf)

    def register_name_tokens(self, decls: list) -> None:
        """Register a discriminator for each token appearing in any decl's
        NAME (distinct from body tokens; names are stronger signal)."""
        seen: set[str] = set()
        for d in decls:
            from align_perspectives import normalize_name  # local import to avoid cycle
            for t in normalize_name(d.name.split(".")[-1] if "." in d.name else d.name):
                if t not in seen:
                    seen.add(t)
                    self._register("name_tok", t, weight=3.0)
                    # Also register any leading-path-segment tokens
            for t in normalize_name(d.name):
                if t not in seen:
                    seen.add(t)
                    self._register("name_tok", t, weight=2.0)

    def register_kinds_and_edges(self, decls: list) -> None:
        """Register one discriminator per (source, kind) and per
        (source, parent_kind, child_kind) edge observed in the corpus."""
        # Source-qualified so they don't collide across parsers.
        kind_freq: Counter = Counter()
        edge_freq: Counter = Counter()
        for d in decls:
            # Every kind in child_sig is a grade-2 "has-child-of-kind-K" signal.
            for field, child_kind in d.child_sig:
                kind_freq[(d.source, child_kind)] += 1
                # Edge from decl.kind → child_kind
                edge_freq[(d.source, d.kind, child_kind)] += 1
            kind_freq[(d.source, d.kind)] += 1
        total = max(sum(kind_freq.values()), 1)
        for (src, k), c in kind_freq.items():
            w = math.log(total / c) + 1.0
            self._register("kind", f"{src}/{k}", weight=w)
        for (src, p, c_), cnt in edge_freq.items():
            w = math.log(total / cnt) + 1.0
            self._register("edge", f"{src}/{p}>{c_}", weight=w)

    def register_citations(self, paper_rows: list[dict]) -> None:
        """For each paper decl with a numeric citation, register two
        discriminators (long-form ``Definition 1.1`` and short-form
        ``Def 1.1``).  These fire when the literal citation appears
        in another decl's docstring."""
        kind_to_names = {
            "definition": ("Definition", "Def"),
            "theorem": ("Theorem", "Thm"),
            "proposition": ("Proposition", "Prop"),
            "lemma": ("Lemma", "Lem"),
            "corollary": ("Corollary", "Cor"),
            "remark": ("Remark", "Rem"),
            "example": ("Example", "Ex"),
            "conjecture": ("Conjecture", "Conj"),
        }
        for r in paper_rows:
            section_num = r.get("section_num")
            item_num = r.get("item_num")
            if not section_num or not item_num:
                continue
            long_form, short_form = kind_to_names.get(r["kind"], (r["kind"].title(), r["kind"][:3].title()))
            cid = f"{section_num}.{item_num}"
            self._register("cite", f"{long_form} {cid}", weight=4.0)
            self._register("cite", f"{short_form} {cid}", weight=4.0)

    def size(self) -> int:
        return len(self._by_id)

    def weights(self) -> list[float]:
        return [d.weight for d in self._by_id]

    def by_family(self) -> dict[str, int]:
        out: Counter = Counter()
        for d in self._by_id:
            out[d.family] += 1
        return dict(out)

    # -----------------------------------------------------------------
    # Per-decl bitmap construction
    # -----------------------------------------------------------------

    def fire_bitmap(
        self,
        decl,
        *,
        docstring: str = "",
    ) -> int:
        """Return the integer bitmask of discriminators that fire on ``decl``.

        ``decl.tokens`` is expected (body normalized tokens).  ``docstring``
        is the raw docstring text used only for ``cite`` family matching.
        """
        bm = 0
        from align_perspectives import normalize_name

        # token/ family
        for t in decl.tokens:
            bid = self._by_key.get(("token", t))
            if bid is not None:
                bm |= 1 << bid

        # name_tok/ family (decl name only)
        for t in normalize_name(decl.name.split(".")[-1] if "." in decl.name else decl.name):
            bid = self._by_key.get(("name_tok", t))
            if bid is not None:
                bm |= 1 << bid
        for t in normalize_name(decl.name):
            bid = self._by_key.get(("name_tok", t))
            if bid is not None:
                bm |= 1 << bid

        # kind/ family (decl's own kind and children's kinds)
        bid = self._by_key.get(("kind", f"{decl.source}/{decl.kind}"))
        if bid is not None:
            bm |= 1 << bid
        for _field, ckind in decl.child_sig:
            bid = self._by_key.get(("kind", f"{decl.source}/{ckind}"))
            if bid is not None:
                bm |= 1 << bid

        # edge/ family (decl's direct parent→child edges)
        for _field, ckind in decl.child_sig:
            bid = self._by_key.get(("edge", f"{decl.source}/{decl.kind}>{ckind}"))
            if bid is not None:
                bm |= 1 << bid

        # cite/ family — requires docstring substring matching.  This
        # firing depends on docstring text, which pandoc/tree-sitter/ast
        # already parsed.  We search for literal citation strings.
        if docstring:
            for (fam, key), bid in self._by_key.items():
                if fam != "cite":
                    continue
                if key in docstring:
                    bm |= 1 << bid

        return bm

    # -----------------------------------------------------------------
    # Weighted popcount for pair scoring
    # -----------------------------------------------------------------

    def weighted_popcount(self, bm: int) -> float:
        """Sum the weights of all discriminators firing in ``bm``."""
        total = 0.0
        # Iterate set bits
        x = bm
        while x:
            lsb = x & -x
            bid = lsb.bit_length() - 1
            total += self._by_id[bid].weight
            x &= x - 1
        return total

    def firing_families(self, bm: int) -> Counter:
        """Per-family count of firings, for human-readable explanations."""
        out: Counter = Counter()
        x = bm
        while x:
            lsb = x & -x
            bid = lsb.bit_length() - 1
            out[self._by_id[bid].family] += 1
            x &= x - 1
        return out
