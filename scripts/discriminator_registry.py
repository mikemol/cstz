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

    ``lexical_mask`` — when True, all string-derived families (``token``,
    ``name_tok``, ``cite``) are disabled.  Only structural (AST-derived)
    discriminators are registered: ``kind``, ``edge``, and any wedges
    the κ-evolution loop articulates.  This mode answers: "how much
    alignment signal is purely structural vs. lexical coincidence?"
    """

    def __init__(self, lexical_mask: bool = False) -> None:
        self._by_id: list[Discriminator] = []
        self._by_key: dict[tuple[str, str], int] = {}
        self.lexical_mask = lexical_mask

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
        appearing in any decl's normalized token bag.

        No-op under ``lexical_mask=True`` (string-derived family).
        """
        if self.lexical_mask:
            return
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
        NAME (distinct from body tokens; names are stronger signal).

        No-op under ``lexical_mask=True`` (string-derived family).
        """
        if self.lexical_mask:
            return
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
        """Register primitive K's derived from the full subtree of each
        decl.  Per user directive ("go two-deep, supersample"):

        kind/K    — every descendant-kind anywhere in the decl's subtree
                    (not just direct children).  These are the AB primitives
                    at tree depth 1: "is there a descendant of kind K?"
        edge/B>C  — every parent→child edge anywhere in the decl's
                    subtree (the BC primitives).  Paths A→B and B→C
                    become primitive; AB-BC composition emerges as a
                    grade-2 wedge in κ-evolution.
        source/S  — source provenance as its own grade-1 K; wedges
                    of source/S ∧ kind/K reproduce source-qualified
                    kinds organically, without being hardcoded.
        """
        kind_freq: Counter = Counter()
        edge_freq: Counter = Counter()
        source_freq: Counter = Counter()
        for d in decls:
            # Prefer full-depth deep_kinds / deep_edges if present
            # (populated by align_perspectives._decl_from_*); fall
            # back to child_sig otherwise.
            if getattr(d, "deep_kinds", None):
                for k in d.deep_kinds:
                    kind_freq[k] += 1
            else:
                kind_freq[d.kind] += 1
                for _f, ck in d.child_sig:
                    kind_freq[ck] += 1
            if getattr(d, "deep_edges", None):
                for (p, c) in d.deep_edges:
                    edge_freq[(p, c)] += 1
            else:
                for _f, ck in d.child_sig:
                    edge_freq[(d.kind, ck)] += 1
            source_freq[d.source] += 1

        total = max(sum(kind_freq.values()), 1)

        for k, c in kind_freq.items():
            w = math.log(total / c) + 1.0
            self._register("kind", k, weight=w)
        for (p, c_), cnt in edge_freq.items():
            w = math.log(total / cnt) + 1.0
            self._register("edge", f"{p}>{c_}", weight=w)

        # source/ family — dependent-type K for decl provenance
        n_total = sum(source_freq.values()) or 1
        for src, c in source_freq.items():
            w = math.log(n_total / c) + 1.0
            self._register("source", src, weight=w)

    def register_citations(self, paper_rows: list[dict]) -> None:
        """For each paper decl with a numeric citation, register two
        discriminators (long-form ``Definition 1.1`` and short-form
        ``Def 1.1``) AND record the paper qualname that "owns" each
        so we can unconditionally fire those bits on the owning decl.

        The discriminator fires:
          * on the paper decl itself (by identity — it IS the cited object)
          * on any other decl whose docstring contains the citation string

        No-op under ``lexical_mask=True`` (string-derived family).
        """
        if self.lexical_mask:
            self._paper_owned_cites = {}
            return
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
        # paper_qualname → set of (family, key) pairs it owns
        self._paper_owned_cites: dict[str, list[tuple[str, str]]] = {}
        for r in paper_rows:
            section_num = r.get("section_num")
            item_num = r.get("item_num")
            label = r.get("label") or ""
            if not section_num or not item_num:
                continue
            long_form, short_form = kind_to_names.get(r["kind"], (r["kind"].title(), r["kind"][:3].title()))
            cid = f"{section_num}.{item_num}"
            self._register("cite", f"{long_form} {cid}", weight=4.0)
            self._register("cite", f"{short_form} {cid}", weight=4.0)
            if label:
                owner_qn = f"paper:{r['kind']}:{label}"
                self._paper_owned_cites.setdefault(owner_qn, []).extend([
                    ("cite", f"{long_form} {cid}"),
                    ("cite", f"{short_form} {cid}"),
                ])

    def register_wedge(
        self,
        family_a: str, key_a: str,
        family_b: str, key_b: str,
        weight: float,
        grade: int = 2,
    ) -> int | None:
        """Register a grade-k wedge of two existing discriminators.

        The wedge discriminator fires iff BOTH parent discriminators
        fire on the same decl.  This is exactly the paper's
        ``d_a ∧ d_b`` in sparse form: its firing set is the AND of
        the parents' firing sets.

        Returns the new discriminator's id, or None if either parent
        isn't registered.  Stored with family tag ``wedge_g{grade}``
        and key ``a|FAMILY_A/KEY_A__b|FAMILY_B/KEY_B`` so the source
        components can be recovered.
        """
        bid_a = self._by_key.get((family_a, key_a))
        bid_b = self._by_key.get((family_b, key_b))
        if bid_a is None or bid_b is None:
            return None
        key = f"{family_a}/{key_a}∧{family_b}/{key_b}"
        family_tag = f"wedge_g{grade}"
        if (family_tag, key) in self._by_key:
            return self._by_key[(family_tag, key)]
        bid = self._register(family_tag, key, weight=weight)
        # Stash parent bits for bitmap-building
        if not hasattr(self, "_wedge_parents"):
            self._wedge_parents: dict[int, tuple[int, int]] = {}
        self._wedge_parents[bid] = (bid_a, bid_b)
        return bid

    def register_candidate_family(
        self, family_tag: str, items: list[tuple[str, float]]
    ) -> int:
        """Register every (key, weight) pair for a candidate family.

        Used by the κ-evolution loop in ``calibrate_weights.py`` to
        articulate new discriminator families when the existing basis
        plateaus.  ``family_tag`` is the generator's family name (e.g.
        ``"name_bigram"``, ``"path_segment"``).

        Returns the count of newly-registered discriminators.
        """
        count = 0
        for key, weight in items:
            if ((family_tag, key)) not in self._by_key:
                self._register(family_tag, key, weight=weight)
                count += 1
        return count

    def ids_by_family(self, family_tag: str) -> list[int]:
        return [d.id for d in self._by_id if d.family == family_tag]

    def drop_family(self, family_tag: str) -> None:
        """Remove every discriminator in the given family.

        Used by SVD-driven orthogonalization when a family is found to
        be rank-deficient.  Compacts ids — so call ``recompute_bitmaps``
        after.  In practice we leave the allocation but zero the weight;
        that preserves bit IDs of the other families.
        """
        for d in list(self._by_id):
            if d.family == family_tag:
                # Replace with zero-weight marker so bitmap bit is still
                # valid but contributes nothing to weighted_popcount.
                self._by_id[d.id] = Discriminator(
                    id=d.id, family=f"{family_tag}_DROPPED", key=d.key, weight=0.0
                )
                self._by_key.pop((family_tag, d.key), None)
                self._by_key[(f"{family_tag}_DROPPED", d.key)] = d.id

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
        extra_families: dict | None = None,
    ) -> int:
        """Return the integer bitmask of discriminators that fire on ``decl``.

        ``decl.tokens`` is expected (body normalized tokens).  ``docstring``
        is the raw docstring text used only for ``cite`` family matching.
        """
        bm = 0
        from align_perspectives import normalize_name

        lexical_mask = getattr(self, "lexical_mask", False)

        # token/ family (string-derived)
        if not lexical_mask:
            for t in decl.tokens:
                bid = self._by_key.get(("token", t))
                if bid is not None:
                    bm |= 1 << bid

        # name_tok/ family (string-derived — decl name only)
        if not lexical_mask:
            for t in normalize_name(decl.name.split(".")[-1] if "." in decl.name else decl.name):
                bid = self._by_key.get(("name_tok", t))
                if bid is not None:
                    bm |= 1 << bid
            for t in normalize_name(decl.name):
                bid = self._by_key.get(("name_tok", t))
                if bid is not None:
                    bm |= 1 << bid

        # kind/ family (structural; full-subtree kinds, not just direct
        # children — the AB primitives per user direction)
        deep_kinds = getattr(decl, "deep_kinds", None) or frozenset()
        if deep_kinds:
            for k in deep_kinds:
                bid = self._by_key.get(("kind", k))
                if bid is not None:
                    bm |= 1 << bid
        else:
            bid = self._by_key.get(("kind", decl.kind))
            if bid is not None:
                bm |= 1 << bid
            for _f, ck in decl.child_sig:
                bid = self._by_key.get(("kind", ck))
                if bid is not None:
                    bm |= 1 << bid

        # edge/ family (structural; full-subtree edges — the BC primitives)
        deep_edges = getattr(decl, "deep_edges", None) or frozenset()
        if deep_edges:
            for (p, c) in deep_edges:
                bid = self._by_key.get(("edge", f"{p}>{c}"))
                if bid is not None:
                    bm |= 1 << bid
        else:
            for _f, ck in decl.child_sig:
                bid = self._by_key.get(("edge", f"{decl.kind}>{ck}"))
                if bid is not None:
                    bm |= 1 << bid

        # source/ family — grade-1 dependent-type K for provenance;
        # wedges of source/SRC ∧ kind/K reproduce the old
        # source-qualified kinds on demand (emergent, not hardcoded).
        bid = self._by_key.get(("source", decl.source))
        if bid is not None:
            bm |= 1 << bid

        # cite/ family (string-derived — citation substrings in docstring)
        if not lexical_mask:
            owned = getattr(self, "_paper_owned_cites", {}).get(decl.qualname, [])
            for key_pair in owned:
                bid = self._by_key.get(key_pair)
                if bid is not None:
                    bm |= 1 << bid
            if docstring:
                for (fam, key), bid in self._by_key.items():
                    if fam != "cite":
                        continue
                    if key in docstring:
                        bm |= 1 << bid

        # --- extra_families: candidate families added via κ-evolution ---
        if extra_families:
            # ``extra_families`` maps family_tag → fire-check callable.
            # We iterate registered discriminators once and invoke the
            # matching fire-check for each.
            for (fam, key), bid in self._by_key.items():
                fire_fn = extra_families.get(fam)
                if fire_fn is None:
                    continue
                try:
                    if fire_fn(decl, key, docstring=docstring):
                        bm |= 1 << bid
                except TypeError:
                    # Some fire functions don't accept docstring kwarg
                    if fire_fn(decl, key):
                        bm |= 1 << bid

        # --- wedge grades: fire iff BOTH parents fire ---
        # Grade-k wedges are AND of their grade-1 (or lower-grade)
        # parents.  We apply them AFTER all grade-1 bits are set.
        # Parents may themselves be wedges (recursive via stored pair).
        wedge_parents = getattr(self, "_wedge_parents", None)
        if wedge_parents:
            # Iterate in registration order so any higher-grade wedge
            # built on a grade-2 parent sees its parent's bit already.
            for bid in sorted(wedge_parents.keys()):
                pa, pb = wedge_parents[bid]
                if ((bm >> pa) & 1) and ((bm >> pb) & 1):
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
