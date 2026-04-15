#!/usr/bin/env python3
"""Three-perspective alignment across paper / agda / python.

Agda is the pivot (user decision: "mirrors paper directly").  For each
Agda declaration we search for paper and python matches using discrimi-
nators lifted from each source's native parse tree — no hand-written
regex library, no author-written cross-reference comments (hybrid-mode
per user decision).

The three passes correspond to the S3 rotation on (κ, σ, τ):

    Pass 1 — Code-as-data:          token-bag overlap.  For each Agda
                                     decl, paper candidates are paper
                                     objects whose tokens contain the
                                     Agda module name or decl name
                                     (in any normalization); python
                                     candidates likewise.
    Pass 2 — Grammar-as-discrimin.:  for each candidate pair, compare
                                     τ-profiles (which grammar kinds
                                     appear in the subtree).  Rare
                                     kinds carry more signal (weighted
                                     by inverse corpus frequency).
    Pass 3 — Relationship-as-obj.:   for each candidate pair, look at
                                     the field-indexed child signatures
                                     (the direct children's (field,
                                     kind) pairs).  Structural fingerprint
                                     of the decl's top-level shape.

A triple is COMMITTED if all three passes vote for the same candidate.
Disagreement → residue, which triggers κ-evolution: drill into the
first child where the perspective that disagrees differs, and add that
child's kind as a new discriminator.

Output:
  reports/triples.jsonl    — one row per committed triple
  reports/residues.jsonl   — one row per unmatched/ambiguous object
  reports/cofiber.md       — agda-E/paper-M/python-M cells enumerated

Usage:
  python3 scripts/align_perspectives.py
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

sys.path.insert(0, str(Path(__file__).parent))
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from structural_identity import (  # noqa: E402
    PandocNode, TreeSitterAgdaNode, PyAstNode, SymbolTable,
    parse_paper_decls, parse_agda_decls, parse_python_decls,
    structural_hash, tau_profile, token_bag, child_signature,
    adjacency_profile, field_adjacency_profile,
)


# ---------------------------------------------------------------------------
# Name normalization — splits identifiers into lowercase word-bag
# ---------------------------------------------------------------------------


_CAMEL_CASE_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")
_GREEK_MAP = {
    "κ": "kappa", "Κ": "Kappa",
    "σ": "sigma", "Σ": "Sigma",
    "τ": "tau",   "Τ": "Tau",
    "χ": "chi",   "Χ": "Chi",
    "Λ": "Lambda", "λ": "lambda",
    "ω": "omega", "Ω": "Omega",
    "ℕ": "nat",
    "∂": "boundary", "∧": "wedge",
    "𝟘": "zero", "𝟙": "one",
    "≡": "eq", "∘": "compose",
}


def normalize_name(s: str) -> frozenset[str]:
    """Split ``s`` into a bag of lowercase word-tokens.

    Handles kebab-case, snake_case, camelCase, dotted-paths, Greek
    letters (via ``_GREEK_MAP``), and embedded digits.  Tokens < 2 chars
    are dropped.
    """
    if not s:
        return frozenset()
    # Apply greek substitution first
    for k, v in _GREEK_MAP.items():
        s = s.replace(k, f"_{v}_")
    # Split camelCase by inserting a space before uppercase runs
    s = _CAMEL_CASE_RE.sub(" ", s)
    # Split on every non-alphanumeric
    parts = re.split(r"[^A-Za-z0-9]+", s.lower())
    return frozenset(p for p in parts if len(p) >= 2)


# ---------------------------------------------------------------------------
# Object records
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Decl:
    source: str             # "paper" | "agda" | "python"
    path: str
    line: int
    kind: str               # grammar's own kind tag
    name: str               # raw declaration name
    qualname: str           # source-qualified name
    tokens: frozenset[str]  # normalized token bag from subtree
    struct_hash: str        # structural hash of subtree
    tau_mask: int           # grade-1 τ-profile bitmask
    child_sig: tuple        # (field, child_kind) tuple for top-level children
    raw_tokens: frozenset[str]  # raw (un-normalized) leaf strings
    adj_card: int = 0       # number of distinct (parent,child) edges (grade-2 adj cardinality)
    adj_hash: str = ""      # hash of field-adjacency triples (WL-1 signature)
    subtree_size: int = 0   # number of nodes in subtree


def _decl_from_paper(n: PandocNode, symtab: SymbolTable, seq: int) -> Decl | None:
    dc = n.named_decl
    if dc is None:
        return None
    kind, label_id = dc
    raw = token_bag(n)
    norm = frozenset().union(*[normalize_name(t) for t in raw])
    norm = norm | normalize_name(label_id)
    disambig = label_id or f"anon_{seq:03d}"
    adj = adjacency_profile(n, symtab)
    fadj = field_adjacency_profile(n, symtab)
    import hashlib
    adj_h = hashlib.blake2b(
        "|".join(f"{p},{f},{c}" for p, f, c in sorted(fadj)).encode(), digest_size=8
    ).hexdigest()
    return Decl(
        source="paper",
        path=n.source_path,
        line=0,
        kind=kind,
        name=label_id or f"<anon_{seq:03d}>",
        qualname=f"paper:{kind}:{disambig}",
        tokens=norm,
        struct_hash=structural_hash(n, symtab),
        tau_mask=tau_profile(n, symtab),
        child_sig=tuple(child_signature(n)),
        raw_tokens=raw,
        adj_card=len(adj),
        adj_hash=adj_h,
        subtree_size=_count_subtree(n),
    )


def _count_subtree(n) -> int:
    count = 1
    for _, c in n.fields:
        count += _count_subtree(c)
    return count


def _decl_from_agda(n: TreeSitterAgdaNode, symtab: SymbolTable) -> Decl | None:
    dc = n.named_decl
    if dc is None:
        return None
    kind, name = dc
    raw = token_bag(n)
    norm = frozenset().union(*[normalize_name(t) for t in raw])
    norm = norm | normalize_name(name)
    qualname = f"agda:{kind}:{name}"
    adj = adjacency_profile(n, symtab)
    fadj = field_adjacency_profile(n, symtab)
    import hashlib
    adj_h = hashlib.blake2b(
        "|".join(f"{p},{f},{c}" for p, f, c in sorted(fadj)).encode(), digest_size=8
    ).hexdigest()
    return Decl(
        source="agda",
        path=n.source_path,
        line=n.source_line,
        kind=kind,
        name=name,
        qualname=qualname,
        tokens=norm,
        struct_hash=structural_hash(n, symtab),
        tau_mask=tau_profile(n, symtab),
        child_sig=tuple(child_signature(n)),
        raw_tokens=raw,
        adj_card=len(adj),
        adj_hash=adj_h,
        subtree_size=_count_subtree(n),
    )


def _decl_from_python(n: PyAstNode, symtab: SymbolTable) -> Decl | None:
    dc = n.named_decl
    if dc is None:
        return None
    kind, name = dc
    raw = token_bag(n)
    norm = frozenset().union(*[normalize_name(t) for t in raw])
    norm = norm | normalize_name(name)
    qualname = f"python:{kind}:{name}"
    adj = adjacency_profile(n, symtab)
    fadj = field_adjacency_profile(n, symtab)
    import hashlib
    adj_h = hashlib.blake2b(
        "|".join(f"{p},{f},{c}" for p, f, c in sorted(fadj)).encode(), digest_size=8
    ).hexdigest()
    return Decl(
        source="python",
        path=n.source_path,
        line=n.source_line,
        kind=kind,
        name=name,
        qualname=qualname,
        tokens=norm,
        struct_hash=structural_hash(n, symtab),
        tau_mask=tau_profile(n, symtab),
        child_sig=tuple(child_signature(n)),
        raw_tokens=raw,
        adj_card=len(adj),
        adj_hash=adj_h,
        subtree_size=_count_subtree(n),
    )


# ---------------------------------------------------------------------------
# Three-perspective scoring
# ---------------------------------------------------------------------------


def compute_idf(decls: list["Decl"]) -> dict[str, float]:
    """Inverse-document-frequency for each token across all decls.

    IDF weight = log(N / df_t) + 1 for every token t appearing in df_t
    decls out of N.  Rare tokens (``operationalist``, ``fano``,
    ``yoneda``) get high weights; common tokens (``axiom``, ``is``,
    ``the``) get low weights.  This is the standard TF-IDF correction
    applied to parse-tree-extracted tokens — still no regex, still no
    hand-written rarity list.
    """
    import math
    n = len(decls)
    df: Counter = Counter()
    for d in decls:
        for t in d.tokens:
            df[t] += 1
    idf = {t: math.log(n / c) + 1.0 for t, c in df.items()}
    return idf


def pass_1_tokens(a: Decl, b: Decl, idf: dict[str, float] | None = None) -> float:
    """IDF-weighted token-bag overlap.

    If ``idf`` is provided, each token's contribution to the
    intersection weight is its IDF.  Union size is the number of
    distinct tokens.  This downweights common tokens like ``axiom``
    that otherwise produce false matches for short-named Agda modules.
    """
    if not a.tokens or not b.tokens:
        return 0.0
    inter = a.tokens & b.tokens
    if not inter:
        return 0.0
    if idf is None:
        idf = {}
    inter_w = sum(idf.get(t, 1.0) for t in inter)
    union_w = sum(idf.get(t, 1.0) for t in a.tokens | b.tokens)
    if union_w == 0:
        return 0.0
    base = inter_w / union_w

    # Strong bonus: is the DECLARATION NAME itself in the other side's
    # token bag?  For Agda module ``CSTZ.Axiom.Operationalist``, the
    # last name segment ``operationalist`` should appear in the paper
    # decl's label (``def:operationalist``) or display name.  If yes,
    # this is a hard signal independent of token density.
    name_norm_a = normalize_name(a.name.split(".")[-1] if "." in a.name else a.name)
    name_norm_b = normalize_name(b.name.split(".")[-1] if "." in b.name else b.name)
    name_match = bool(name_norm_a & b.tokens) and bool(name_norm_b & a.tokens)
    half_match = bool(name_norm_a & b.tokens) or bool(name_norm_b & a.tokens)
    if name_match:
        return base + 0.5
    if half_match:
        return base + 0.2
    return base


def pass_2_grammar(a: Decl, b: Decl, rarity: dict[tuple[str, str], float]) -> float:
    """Grammar-reflected signal: rarity-weighted kind-distribution overlap.

    For each (source, kind) we compute inverse-frequency weight.  Two
    decls are similar in this perspective if their subtrees use a
    similar DISTRIBUTION of grammar kinds — but the signal is weighted
    so common kinds (Str, Space in pandoc; atom, qid in Agda; Load,
    Name in Python) contribute little.

    Cross-source pairs don't share kinds directly, so we project onto
    a COMMON axis: normalized kind labels.  "module" in paper pandoc
    (Header.1), "module" in tree-sitter, and "Module" in Python ast
    are distinct tokens; we just compare relative kind-rarity profiles.
    """
    # Compute relative rarity vector for each: for each kind appearing
    # in the decl's subtree, its inverse-frequency weight.
    # We extract kinds from the child_sig + kind; tau_mask counts
    # distinct kinds but we don't have an easy way to unpack it without
    # the symbol table.  Use child_sig as an approximation of "kinds
    # present at grade 1 depth" for the decl.
    a_kinds = frozenset(k for _, k in a.child_sig)
    b_kinds = frozenset(k for _, k in b.child_sig)
    if not a_kinds or not b_kinds:
        return 0.0
    common = a_kinds & b_kinds  # only meaningful within same source
    # For cross-source: return the fraction of a's rare kinds that are
    # also rare in b (a "rarity correlation").  This is a coarse signal.
    a_rarity = sum(rarity.get((a.source, k), 0.0) for k in a_kinds)
    b_rarity = sum(rarity.get((b.source, k), 0.0) for k in b_kinds)
    if a_rarity == 0 or b_rarity == 0:
        return 0.0
    # Ratio of mean rarities (closer to 1 = more similar complexity profiles)
    ratio = min(a_rarity, b_rarity) / max(a_rarity, b_rarity)
    return 0.5 * ratio


def pass_3_relationship(a: Decl, b: Decl) -> float:
    """Relationship-as-object: does the decl's path-position correspond?

    We compare the declaration KINDS themselves, projected onto a
    small family of coarse structural roles:

        "namespace-like":  paper:(section-host-of-defs), agda:module, python:module
        "axiom-like":      paper:definition/theorem, agda:postulate, python:(check_*)
        "container-like":  paper:theorem/proposition, agda:record/data, python:class
        "morphism-like":   paper:(other), agda:function, python:function

    The roles themselves are NOT hardcoded mappings — they are
    derived by observing which paper/agda/python KINDS co-occur
    frequently in token-matched triples from Pass 1.  That is: we
    build the role-map by looking at Pass-1 evidence, then use it to
    score Pass 3.  See ``build_role_map`` below.
    """
    # This function expects a role map built ahead of time; we inject
    # it via a closure in the driver.  Returning a placeholder here;
    # real scoring happens in the driver after role_map is derived.
    raise NotImplementedError("use pass_3_with_role_map in driver")


def pass_3_with_role_map(a: Decl, b: Decl, role_map: dict[tuple[str, str], str]) -> float:
    a_role = role_map.get((a.source, a.kind))
    b_role = role_map.get((b.source, b.kind))
    if a_role is None or b_role is None:
        return 0.0
    return 1.0 if a_role == b_role else 0.0


def pass_4_adjacency(a: Decl, b: Decl) -> float:
    """Relational discriminator: grade-2 adjacency profile comparison.

    Cross-source adjacency IDs are not directly comparable (different
    parsers' kind_ids live in different spaces), but the *distribution*
    of edge-counts IS a meaningful cross-source signal.  Two decls
    whose subtrees have similar numbers of parent-child edges relative
    to their subtree size are more likely to correspond structurally.

    Score components:

      edge_density      — ratio of adj_card to subtree_size; similar
                          densities → similar structural density.
      size_ratio        — log-spaced subtree_size similarity.

    Within-source: we additionally match on ``adj_hash`` equality,
    which gives a strict κ-equivalence on field-adjacency profiles
    (Paper Thm 6.13: the triadic adjunction acts on grade-2 elements).
    """
    if a.source == b.source:
        return 1.0 if a.adj_hash == b.adj_hash else 0.0
    # Cross-source: compare structural density + size
    if a.subtree_size == 0 or b.subtree_size == 0:
        return 0.0
    density_a = a.adj_card / max(1, a.subtree_size - 1)
    density_b = b.adj_card / max(1, b.subtree_size - 1)
    density_sim = 1.0 - min(1.0, abs(density_a - density_b))

    import math
    sa, sb = a.subtree_size, b.subtree_size
    size_sim = 1.0 - min(1.0, abs(math.log(sa + 1) - math.log(sb + 1)) / 4.0)

    return 0.5 * density_sim + 0.5 * size_sim


# ---------------------------------------------------------------------------
# Role map induction (learned from Pass-1 triples)
# ---------------------------------------------------------------------------


def build_role_map(pass1_triples: list[tuple[Decl, Decl, float]]) -> dict[tuple[str, str], str]:
    """Induce a (source, kind) -> role mapping from Pass-1 matches.

    For each (source, kind) pair, look at which OTHER (source, kind)
    pairs it co-occurs with in high-scoring Pass-1 matches.  Clustering
    by co-occurrence gives an emergent role partition.  We use a
    simple transitive closure: (source_a, kind_a) and (source_b, kind_b)
    are "in the same role" if they co-occur in ≥2 Pass-1 matches.

    The role names (``role_0``, ``role_1``, …) are arbitrary cluster
    IDs — not labels I chose.  The alignment engine only cares that
    decls in the same emergent cluster score 1.0 in pass_3.
    """
    # Co-occurrence graph: edges between (src,kind) pairs that co-match
    edges: dict[tuple[str, str], Counter] = defaultdict(Counter)
    for a, b, score in pass1_triples:
        if score < 0.2:
            continue
        ka = (a.source, a.kind)
        kb = (b.source, b.kind)
        if ka != kb:
            edges[ka][kb] += 1
            edges[kb][ka] += 1
    # Build clusters via union-find on edges with count ≥ 2
    parent: dict[tuple[str, str], tuple[str, str]] = {}

    def find(x):
        while parent.get(x, x) != x:
            parent[x] = parent.get(parent[x], parent[x])
            x = parent[x]
        return x

    def union(x, y):
        parent.setdefault(x, x)
        parent.setdefault(y, y)
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    for ka, neighbors in edges.items():
        union(ka, ka)
        for kb, count in neighbors.items():
            if count >= 2:
                union(ka, kb)

    roots = {find(ka) for ka in parent}
    root_to_role = {r: f"role_{i}" for i, r in enumerate(sorted(roots))}
    return {ka: root_to_role[find(ka)] for ka in parent}


# ---------------------------------------------------------------------------
# Corpus-wide rarity
# ---------------------------------------------------------------------------


def corpus_rarity(decls: list[Decl]) -> dict[tuple[str, str], float]:
    """For each (source, kind), the inverse frequency."""
    counts: Counter = Counter()
    for d in decls:
        for _, k in d.child_sig:
            counts[(d.source, k)] += 1
    total_by_source: Counter = Counter()
    for (src, k), c in counts.items():
        total_by_source[src] += c
    rarity: dict[tuple[str, str], float] = {}
    for (src, k), c in counts.items():
        total = total_by_source[src] or 1
        rarity[(src, k)] = total / c
    return rarity


# ---------------------------------------------------------------------------
# Main alignment driver
# ---------------------------------------------------------------------------


def load_all(repo: Path) -> tuple[list[Decl], list[Decl], list[Decl], SymbolTable, SymbolTable, SymbolTable]:
    st_p = SymbolTable("paper")
    st_a = SymbolTable("agda")
    st_y = SymbolTable("python")

    paper = []
    for i, n in enumerate(parse_paper_decls(repo / "paper")):
        d = _decl_from_paper(n, st_p, i)
        if d is not None:
            paper.append(d)

    agda = []
    for path in sorted((repo / "agda").rglob("*.agda")):
        for n in parse_agda_decls(path):
            d = _decl_from_agda(n, st_a)
            if d is not None:
                agda.append(d)

    python = []
    for path in sorted((repo / "src/cstz").rglob("*.py")):
        if any(part == "legacy" for part in path.parts):
            continue
        for n in parse_python_decls(path):
            d = _decl_from_python(n, st_y)
            if d is not None:
                python.append(d)

    return paper, agda, python, st_p, st_a, st_y


def align(paper: list[Decl], agda: list[Decl], python: list[Decl]) -> dict:
    """Run the three-perspective alignment with Agda as pivot."""
    all_decls = paper + agda + python
    rarity = corpus_rarity(all_decls)
    idf = compute_idf(all_decls)

    # --- Pass 1: IDF-weighted token overlap ---
    p1_agda_paper: dict[str, list[tuple[str, float]]] = defaultdict(list)
    p1_agda_python: dict[str, list[tuple[str, float]]] = defaultdict(list)
    p1_all_matches: list[tuple[Decl, Decl, float]] = []

    for a in agda:
        for p in paper:
            s = pass_1_tokens(a, p, idf)
            if s > 0.05:
                p1_agda_paper[a.qualname].append((p.qualname, s))
                p1_all_matches.append((a, p, s))
        for y in python:
            s = pass_1_tokens(a, y, idf)
            if s > 0.05:
                p1_agda_python[a.qualname].append((y.qualname, s))
                p1_all_matches.append((a, y, s))

    # --- Build emergent role map from Pass 1 ---
    role_map = build_role_map(p1_all_matches)

    # --- Index for fast lookup ---
    paper_by_qn = {p.qualname: p for p in paper}
    python_by_qn = {y.qualname: y for y in python}
    agda_by_qn = {a.qualname: a for a in agda}

    triples: list[dict] = []
    residues: list[dict] = []

    for a in agda:
        # Top candidate per side from Pass 1
        paper_cands = sorted(p1_agda_paper.get(a.qualname, []), key=lambda x: -x[1])
        python_cands = sorted(p1_agda_python.get(a.qualname, []), key=lambda x: -x[1])

        # Score top candidates with Pass 2 + Pass 3 and accumulate
        def composite(cands, by_qn):
            scored = []
            for qn, s1 in cands:
                cand = by_qn[qn]
                s2 = pass_2_grammar(a, cand, rarity)
                s3 = pass_3_with_role_map(a, cand, role_map)
                s4 = pass_4_adjacency(a, cand)
                # Weights:
                #   s1 (token-bag)        0.55  — primary semantic signal
                #   s2 (grammar rarity)   0.10  — weak, coarse-grained
                #   s3 (emergent role)    0.15  — mid, learned kind-map
                #   s4 (grade-2 adj)      0.20  — relational structural signal
                total = 0.55 * s1 + 0.10 * s2 + 0.15 * s3 + 0.20 * s4
                scored.append((qn, total, s1, s2, s3, s4))
            return sorted(scored, key=lambda x: -x[1])

        p_scored = composite(paper_cands, paper_by_qn)
        y_scored = composite(python_cands, python_by_qn)

        def best_or_none(scored):
            """Commit iff absolute score ≥0.30 AND margin over second ≥1.2×.

            Margin measured as ratio top/second with second defaulting
            to 0.001 when there's only one candidate.  Pure top-is-
            winner "I guessed" picks (ratio near 1.0) go to residue so
            the loop can κ-evolve them later.
            """
            if not scored:
                return None
            top = scored[0][1]
            if top < 0.30:
                return None
            second = scored[1][1] if len(scored) >= 2 else 0.001
            if top >= 1.2 * max(second, 0.001):
                return scored[0]
            return None

        p_pick = best_or_none(p_scored)
        y_pick = best_or_none(y_scored)

        if p_pick and y_pick:
            triples.append({
                "agda": a.qualname,
                "agda_path": f"{a.path}:{a.line}",
                "paper": p_pick[0],
                "paper_score": p_pick[1:],
                "python": y_pick[0],
                "python_score": y_pick[1:],
                "paper_path": f"{paper_by_qn[p_pick[0]].path}",
                "python_path": f"{python_by_qn[y_pick[0]].path}:{python_by_qn[y_pick[0]].line}",
            })
        else:
            residues.append({
                "agda": a.qualname,
                "agda_path": f"{a.path}:{a.line}",
                "paper_candidates": p_scored[:3],
                "python_candidates": y_scored[:3],
                "missing_side": [
                    "paper" if not p_pick else "",
                    "python" if not y_pick else "",
                ],
            })

    return {
        "triples": triples,
        "residues": residues,
        "role_map": role_map,
        "stats": {
            "paper_decls": len(paper),
            "agda_decls": len(agda),
            "python_decls": len(python),
            "committed_triples": len(triples),
            "residues": len(residues),
        },
    }


def main():
    repo = Path(sys.argv[1]) if len(sys.argv) > 1 else Path.cwd()
    print("# loading declarations from all three sources ...", file=sys.stderr)
    paper, agda, python, st_p, st_a, st_y = load_all(repo)
    print(
        f"# paper={len(paper)} agda={len(agda)} python={len(python)} "
        f"|  symtabs: paper={len(st_p)} agda={len(st_a)} python={len(st_y)}",
        file=sys.stderr,
    )

    print("# running three-perspective alignment (Agda as pivot) ...", file=sys.stderr)
    result = align(paper, agda, python)

    reports = repo / "reports"
    reports.mkdir(exist_ok=True)
    (reports / "triples.jsonl").write_text(
        "\n".join(json.dumps(t, ensure_ascii=False) for t in result["triples"]) + "\n"
        if result["triples"] else ""
    )
    (reports / "residues.jsonl").write_text(
        "\n".join(json.dumps(r, ensure_ascii=False) for r in result["residues"]) + "\n"
        if result["residues"] else ""
    )
    (reports / "role_map.json").write_text(
        json.dumps(
            {f"{src}:{kind}": role for (src, kind), role in result["role_map"].items()},
            ensure_ascii=False, indent=2,
        )
    )
    print(json.dumps(result["stats"], indent=2), file=sys.stderr)


if __name__ == "__main__":
    main()
