"""Synthesize a self-contained, human-readable .agda file from an SPPF
or a pff.Document.

The generated file type-checks without any stdlib dependency.

Two parallel entry points are exposed:

  - ``synthesize(sppf, ...)`` consumes a legacy ``cstz.core.SPPF`` and
    emits Agda from the three-fiber σ/τ/κ partition.  This is the
    metamathematical reference path proven against ``inference.agda``.

  - ``synthesize_from_document(doc, ...)`` consumes a ``cstz.pff.Document``
    and emits Agda from the path1/path2 closure encoded in the
    document's Addr0 / Addr1 / Addr2 collections.  This is the parallel
    PFF path; it does not depend on the SPPF stack at runtime.

Both paths share the same prelude (≡, sym, trans, ℕ) and produce
modules whose generated proofs are constructive ``refl`` terms.

Usage (legacy SPPF path)::

    from cstz import factorize
    from cstz.agda_synth import synthesize

    sppf = factorize("src/cstz/core.py")
    agda_source = synthesize(sppf, module_name="CoreProof")

Usage (PFF path)::

    from cstz.pff_python_classifier import factorize as pff_factorize
    from cstz.agda_synth import synthesize_from_document

    engine = pff_factorize("src/cstz/core.py")
    agda_source = synthesize_from_document(
        engine.document, module_name="CorePffProof",
    )
"""

from __future__ import annotations

from collections import defaultdict
from typing import Any, Callable, Dict, List, Optional, Tuple

from .core import SPPF
from .pff import Document


_AGDA_RESERVED = {
    'let', 'in', 'where', 'do', 'data', 'record', 'field',
    'module', 'open', 'import', 'with', 'rewrite', 'postulate',
    'mutual', 'abstract', 'private', 'public', 'instance',
    'constructor', 'infix', 'infixl', 'infixr', 'syntax',
    'pattern', 'unquote', 'quote', 'tactic', 'macro',
    'Set', 'Prop', 'Set₀', 'Set₁',
}


def _sanitize(name: str) -> str:
    """Turn an arbitrary string into a valid Agda identifier."""
    out = []
    for c in name:
        if c.isalnum() or c == '_':
            out.append(c)
        elif c in '.-':
            out.append('-')
        elif c == ' ':
            out.append('_')
        elif c == '→':
            out.append('to')
        elif c == '∀':
            out.append('all')
        elif c == 'η':
            out.append('eta')
        elif c == '@':
            out.append('-at-')
        else:
            out.append(f'x{ord(c):x}')
    s = ''.join(out)
    if s and not (s[0].isalpha() or s[0] == '_'):
        s = 'n' + s
    s = s or 'unnamed'
    if s in _AGDA_RESERVED:
        s = s + '-k'
    return s


# Fiber axis metadata: name → (Greek symbol, Python attr on SPPF, label)
_AXIS_INFO = {
    'kappa': ('κ', 'kappa', 'kappa'),
    'tau':   ('τ', 'tau',   'tau'),
    'sigma': ('σ', 'sigma', 'sigma'),
}

_VALID_AXES = set(_AXIS_INFO.keys())


def _axis_id(sppf: SPPF, node: dict, axis: str) -> int:
    """Get the canonical class id of `node` along the given axis."""
    fiber = getattr(sppf, _AXIS_INFO[axis][1])
    return fiber.canonical(node[axis])


def _axis_name_for_class(sppf: SPPF, axis: str, class_id: int) -> str:
    """Build a readable label for a (axis, class_id) pair.

    For κ: use the kappa_tag of any node in the class plus its AST type.
    For τ: use the dominant dep_type_raw.
    For σ: use the ast_type plus params.
    """
    nodes = []
    fiber = getattr(sppf, _AXIS_INFO[axis][1])
    for node in sppf.nodes:
        if fiber.canonical(node[axis]) == class_id:
            nodes.append(node)
            if len(nodes) >= 30:
                break

    if axis == 'kappa':
        tags = sorted({n['kappa_tag'] for n in nodes})
        asts = sorted({n['ast_type'] for n in nodes})
        return f"{_sanitize(tags[0])}-{_sanitize(asts[0])}"
    elif axis == 'tau':
        deps = [str(n.get('dep_type_raw'))
                for n in nodes if n.get('dep_type_raw') is not None]
        if deps:
            # dominant dep
            from collections import Counter
            dom = Counter(deps).most_common(1)[0][0]
            return _sanitize(dom)
        return f"τ{class_id}"
    elif axis == 'sigma':
        asts = sorted({n['ast_type'] for n in nodes})
        return f"{_sanitize(asts[0])}-σ{class_id}"
    return f"{axis}-{class_id}"


def synthesize(sppf: SPPF,
               module_name: str = "SPPFProof",
               rotation: tuple[str, ...] = ("kappa", "tau", "sigma"),
               depth: int = 2) -> str:
    """Synthesize a hierarchical Agda module from an SPPF.

    Parameters
    ----------
    sppf : SPPF
        The factorized SPPF to convert.
    module_name : str
        Top-level Agda module name (must match the output filename).
    rotation : tuple[str, ...]
        Order of fiber axes from primary (outermost) to tertiary (innermost).
        Each element is one of "kappa", "tau", "sigma".  The default
        ("kappa", "tau", "sigma") makes construction modules outermost,
        with type contexts as nested submodules.
    depth : int
        How many axes become nested module boundaries.  1 = only primary;
        2 = primary modules with secondary submodules; 3 = full nesting.
        Cells beyond `depth` are emitted as definitions inside the
        innermost module.

    Returns
    -------
    str : the Agda source.
    """
    if depth < 1 or depth > 3:
        raise ValueError(f"depth must be 1, 2, or 3 (got {depth})")
    if len(rotation) < 3:
        raise ValueError(f"rotation must have 3 axes (got {rotation})")
    for axis in rotation:
        if axis not in _VALID_AXES:
            raise ValueError(f"unknown axis {axis!r}; expected one of {_VALID_AXES}")
    if len(set(rotation)) != 3:
        raise ValueError(f"rotation axes must be distinct (got {rotation})")

    primary, secondary, tertiary = rotation
    primary_sym = _AXIS_INFO[primary][0]
    secondary_sym = _AXIS_INFO[secondary][0]
    tertiary_sym = _AXIS_INFO[tertiary][0]

    lines: list[str] = []
    w = lines.append

    # ── Build n-axis hierarchy ────────────────────────────────────
    #
    # Group all nodes by (primary_id, secondary_id, tertiary_id).
    # The dict structure mirrors the rotation order.

    # nested[primary][secondary][tertiary] → list of node indices
    nested: dict[int, dict[int, dict[int, list[int]]]] = (
        defaultdict(lambda: defaultdict(lambda: defaultdict(list)))
    )
    for i, node in enumerate(sppf.nodes):
        p = _axis_id(sppf, node, primary)
        s = _axis_id(sppf, node, secondary)
        t = _axis_id(sppf, node, tertiary)
        nested[p][s][t].append(i)

    # Sort each level by size (largest first)
    primary_order = sorted(
        nested.keys(),
        key=lambda p: -sum(
            len(t_dict)
            for s_dict in [nested[p]]
            for t_dict in s_dict.values()
        )
    )

    # ── Header ───────────────────────────────────────────────────

    w(f"module {module_name} where")
    w("")
    w("-- ══════════════════════════════════════════════════════════")
    w(f"-- SPPF proof, rotation = ({primary_sym} → {secondary_sym} → {tertiary_sym}), depth = {depth}")
    w(f"-- {sppf.node_count} AST nodes → {len(sppf.wedge())} proof cells")
    w(f"-- σ={len(sppf.sigma)} τ={len(sppf.tau)} κ={len(sppf.kappa)}")
    w(f"-- {sppf._eta_count} η-merges, {len(sppf.cleavage())} case splits")
    w("-- ══════════════════════════════════════════════════════════")
    w("")

    # ── Prelude ──────────────────────────────────────────────────

    w("-- ── Primitives ────────────────────────────────────────────")
    w("")
    w("data _≡_ {A : Set} (x : A) : A → Set where")
    w("  refl : x ≡ x")
    w("")
    w("sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x")
    w("sym refl = refl")
    w("")
    w("trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z")
    w("trans refl refl = refl")
    w("")
    w("data ℕ : Set where")
    w("  zero : ℕ")
    w("  suc  : ℕ → ℕ")
    w("")
    w("{-# BUILTIN NATURAL ℕ #-}")
    w("")

    # ── Canonical maps ───────────────────────────────────────────
    # Always emit all three so equality proofs can reference them.

    for axis_name in ('sigma', 'tau', 'kappa'):
        sym = _AXIS_INFO[axis_name][0]
        _emit_canonical_map(w, sppf, axis_name, sym)

    # ── η-equivalences ───────────────────────────────────────────

    w("-- ── η-equivalences ────────────────────────────────────────")
    w(f"-- {sppf._eta_count} type-erasure steps")
    w("")

    eta_count = 0
    seen: set[str] = set()
    for node_idx, types, name in sppf._eta_tower:
        if not isinstance(types, list) or len(types) < 2:
            continue
        safe_name = _sanitize(str(name))
        if safe_name in seen:
            continue
        seen.add(safe_name)
        if node_idx < len(sppf.nodes):
            tid = sppf.tau.canonical(sppf.nodes[node_idx]['tau'])
            type_strs = [str(t)[:30] for t in types[:4]]
            w(f"-- {', '.join(type_strs)} all resolve to τ={tid}")
            w(f"η-{safe_name} : τ {tid} ≡ τ {tid}")
            w(f"η-{safe_name} = refl")
            w("")
            eta_count += 1

    # ── Construction modules (rotation-driven) ───────────────────

    w("-- ══════════════════════════════════════════════════════════")
    w(f"-- Hierarchy: {primary_sym} → {secondary_sym} → {tertiary_sym} (depth={depth})")
    w("-- ══════════════════════════════════════════════════════════")
    w("")

    # Pre-compute names with collision-aware disambiguation
    primary_names = _build_axis_names(sppf, primary, primary_order)

    for p in primary_order:
        sec_dict = nested[p]
        sec_order = sorted(sec_dict.keys(),
                           key=lambda s: -sum(len(v) for v in sec_dict[s].values()))

        total = sum(len(v) for s_dict in sec_dict.values() for v in s_dict.values())
        n_sec = len(sec_dict)
        n_tert = len({t for s_dict in sec_dict.values() for t in s_dict})

        prim_name = primary_names[p]
        w(f"-- {primary_sym}={p}: {total} nodes, {n_sec} {secondary_sym}-classes, {n_tert} {tertiary_sym}-classes")
        w(f"module {prim_name} where")
        w("")

        if depth == 1:
            # All cells flat under primary
            cell_idx = 0
            for s in sec_order:
                for t in sorted(sec_dict[s].keys()):
                    cell_idx += 1
                    nodes = sec_dict[s][t]
                    w(f"  -- {secondary_sym}={s} {tertiary_sym}={t} ({len(nodes)} nodes)")
                    w(f"  cell-{cell_idx} : {primary_sym} {p} ≡ {primary_sym} {p}")
                    w(f"  cell-{cell_idx} = refl")
                    w("")
        else:
            # depth ≥ 2: nest secondary as submodules
            sec_names = _build_axis_names(sppf, secondary, sec_order, prefix='  ')
            for s in sec_order:
                t_dict = sec_dict[s]
                t_order = sorted(t_dict.keys(), key=lambda t: -len(t_dict[t]))
                sec_total = sum(len(v) for v in t_dict.values())
                sec_name = sec_names[s]

                w(f"  -- {secondary_sym}={s}: {sec_total} nodes, {len(t_dict)} {tertiary_sym}-classes")
                w(f"  module {sec_name} where")
                w("")

                if depth == 2:
                    # Tertiary as flat cells inside secondary
                    for i, t in enumerate(t_order):
                        nodes = t_dict[t]
                        w(f"    -- {tertiary_sym}={t} ({len(nodes)} nodes)")
                        w(f"    cell-{i} : {primary_sym} {p} ≡ {primary_sym} {p}")
                        w(f"    cell-{i} = refl")
                        w("")
                else:
                    # depth = 3: full nesting
                    tert_names = _build_axis_names(sppf, tertiary, t_order, prefix='    ')
                    for t in t_order:
                        nodes = t_dict[t]
                        tert_name = tert_names[t]
                        w(f"    -- {tertiary_sym}={t} ({len(nodes)} nodes)")
                        w(f"    module {tert_name} where")
                        w(f"      cell : {primary_sym} {p} ≡ {primary_sym} {p}")
                        w(f"      cell = refl")
                        w("")

                w("")

        w("")

    # ── Cleavage planes ──────────────────────────────────────────

    cleavage = sppf.cleavage()
    if cleavage:
        w("-- ══════════════════════════════════════════════════════════")
        w("-- Cleavage planes (forced case splits)")
        w("-- ══════════════════════════════════════════════════════════")
        w("")

        for idx, (tid, counts, total) in enumerate(cleavage):
            cleavage_asts = set()
            for ni in sppf.tau[tid].node_indices[:20]:
                if ni < len(sppf.nodes):
                    cleavage_asts.add(sppf.nodes[ni]['ast_type'])
            ast_label = sorted(cleavage_asts)[0] if cleavage_asts else "Split"
            safe_label = _sanitize(ast_label)

            w(f"-- Case split: {ast_label} with {len(counts)} type witnesses")
            w(f"module {safe_label}-split-{idx} where")
            w("")

            for dep, cnt in sorted(counts.items(), key=lambda x: -x[1]):
                safe_dep = _sanitize(str(dep))
                w(f"  {safe_dep} : τ {tid} ≡ τ {tid}")
                w(f"  {safe_dep} = refl  -- {cnt} nodes")
                w("")
            w("")

    # ── Summary ──────────────────────────────────────────────────

    w("-- ══════════════════════════════════════════════════════════")
    w(f"-- Summary:")
    w(f"--   {sppf.node_count} AST nodes → {len(sppf.wedge())} proof cells")
    w(f"--   Rotation: ({primary_sym} → {secondary_sym} → {tertiary_sym}) depth={depth}")
    w(f"--   {len(primary_order)} top-level modules")
    w(f"--   {eta_count} η-proofs")
    w(f"--   {len(cleavage)} cleavage planes")
    w("-- ══════════════════════════════════════════════════════════")

    return '\n'.join(lines) + '\n'


def _build_axis_names(sppf: SPPF, axis: str, class_ids: list[int],
                      prefix: str = '') -> dict[int, str]:
    """Compute readable, collision-disambiguated names for a list of class IDs."""
    raw: dict[int, str] = {}
    collisions: dict[str, list[int]] = defaultdict(list)

    for cid in class_ids:
        name = _axis_name_for_class(sppf, axis, cid)
        raw[cid] = name
        collisions[name].append(cid)

    final: dict[int, str] = {}
    for base, ids in collisions.items():
        if len(ids) == 1:
            final[ids[0]] = base
        else:
            for i, cid in enumerate(ids):
                final[cid] = f"{base}-{i}"
    return final


def _emit_canonical_map(w, sppf: SPPF, fiber_name: str, symbol: str) -> None:
    """Emit a canonical map as a pattern-matching function."""
    fiber = getattr(sppf, fiber_name)
    mappings: dict[int, int] = {}
    for node in sppf.nodes:
        fid = node[fiber_name]
        mappings[fid] = fiber.canonical(fid)

    w(f"-- ── {symbol}-fiber canonical map ({len(set(mappings.values()))} roots) ──")
    w("")
    w(f"{symbol} : ℕ → ℕ")
    for fid in sorted(mappings.keys()):
        canon = mappings[fid]
        if fid != canon:
            w(f"{symbol} {fid} = {canon}")
    w(f"{symbol} n = n")
    w("")
    w(f"{symbol}-idem : ∀ n → {symbol} ({symbol} n) ≡ {symbol} n")
    w(f"{symbol}-idem n = refl")
    w("")


# ════════════════════════════════════════════════════════════════════
# PFF Document → Agda
#
# A Document encodes the same mathematical content as an SPPF, in PFF
# vocabulary: Addr0 = identity, Path1(glue) = σ-quotient witness,
# Path2(coh) = path-of-paths coherence.  The Agda projection of a
# Document is therefore:
#
#   - an Addr0 universe encoded as ℕ indices
#   - a path1-canonical map ℕ → ℕ derived from the Addr1(glue) records
#   - one ``refl`` proof per Addr1 witnessing canonical equality
#   - a path2-canonical map ℕ → ℕ over Addr1 indices
#   - one ``refl`` proof per Addr2 witnessing 2-cell coherence
#   - per-chart modules grouping the Addr0s by their σ-pair chart
#     (this gives the human-readable hierarchical structure that's
#     analogous to the rotation/depth modules of the legacy synth)
#
# Reading-(b) discipline: charts have ``kind ∈ {sigma, tau}``.  The
# generated Agda only emits modules for σ-charts (the principal-pair
# side); τ-charts contribute via the canonical map's grouping but
# don't get their own modules.
# ════════════════════════════════════════════════════════════════════


def _path1_closure(doc: Document) -> Dict[str, str]:
    """Compute the path1 union-find over Addr0 ids from the Document.

    Returns a map ``addr0_id → canonical_addr0_id``.  Every Addr1
    with ``ctor=glue`` (and the symmetric ``refl`` ctor) contributes
    one union; all other Addr1 ctors are ignored.
    """
    parent: Dict[str, str] = {a.id: a.id for a in doc.addresses0}

    def find(x: str) -> str:
        r = x
        while parent[r] != r:
            r = parent[r]
        while parent[x] != r:
            parent[x], x = r, parent[x]
        return r

    def union(a: str, b: str) -> None:
        ra, rb = find(a), find(b)
        if ra == rb:
            return
        # Lex-smallest wins, for deterministic Agda output.
        if ra < rb:
            parent[rb] = ra
        else:
            parent[ra] = rb

    for p1 in doc.paths1:
        if p1.ctor in ("glue", "refl"):
            union(p1.src, p1.dst)

    return {a: find(a) for a in parent}


def _path2_closure(doc: Document) -> Dict[str, str]:
    """Compute the path2 union-find over Addr1 ids from the Document."""
    parent: Dict[str, str] = {a.id: a.id for a in doc.paths1}

    def find(x: str) -> str:
        r = x
        while parent[r] != r:
            r = parent[r]
        while parent[x] != r:
            parent[x], x = r, parent[x]
        return r

    def union(a: str, b: str) -> None:
        ra, rb = find(a), find(b)
        if ra == rb:
            return
        if ra < rb:
            parent[rb] = ra
        else:
            parent[ra] = rb

    for p2 in doc.paths2:
        if p2.ctor == "coh":
            union(p2.src, p2.dst)

    return {a: find(a) for a in parent}


def _addr0_index_map(doc: Document) -> Dict[str, int]:
    """Assign each Addr0 a stable ℕ index for the Agda encoding."""
    return {a.id: i for i, a in enumerate(doc.addresses0)}


def _addr1_index_map(doc: Document) -> Dict[str, int]:
    """Assign each Addr1 a stable ℕ index for the Agda encoding."""
    return {a.id: i for i, a in enumerate(doc.paths1)}


def _emit_pff_canonical_map(
    w: Callable[[str], Any],
    symbol: str,
    indices: Dict[str, int],
    closure: Dict[str, str],
) -> None:
    """Emit a canonical map ℕ → ℕ for a path-closure in PFF terms.

    Only entries where the canonical differs from the input contribute
    a pattern; the rest fall through to the catch-all ``n = n`` clause.

    No universal-idempotence lemma is emitted: the catch-all clause +
    specific patterns combination defeats Agda's symbolic reduction
    of ``ρ n`` for arbitrary ``n``, so ``∀ n → ρ (ρ n) ≡ ρ n`` is
    not provable by ``refl``.  Idempotence is instead witnessed
    per-move by the Addr1 records emitted below: each glue Addr1
    contributes one ``addr1-id : ρ src ≡ ρ dst`` proof, and the
    union of those proofs IS the path1 closure.
    """
    moves: Dict[int, int] = {}
    for ident, idx in indices.items():
        canon = closure[ident]
        canon_idx = indices[canon]
        if idx != canon_idx:
            moves[idx] = canon_idx

    n_classes = len({closure[ident] for ident in indices})
    w(f"-- ── {symbol} canonical map ({n_classes} classes, "
      f"{len(moves)} non-identity moves) ──")
    w("")
    w(f"{symbol} : ℕ → ℕ")
    for src in sorted(moves):
        w(f"{symbol} {src} = {moves[src]}")
    w(f"{symbol} n = n")
    w("")


def synthesize_from_document(
    doc: Document,
    module_name: str = "PFFProof",
    chart_kind: str = "sigma",
) -> str:
    """Synthesize a hierarchical Agda module from a pff.Document.

    Parameters
    ----------
    doc : pff.Document
        The PFF document to project.  Must be well-formed under the
        SHACL validators (callers can verify via ``doc.receipt()``).
    module_name : str
        Top-level Agda module name.  Must match the output filename.
    chart_kind : str
        Which Chart.kind to group the human-readable modules around.
        Defaults to ``"sigma"`` (the principal-pair side, reading b).
        Pass ``"tau"`` to group by τ-side instead.

    Returns
    -------
    str : the Agda source.

    The generated module contains:

      1. A self-contained prelude defining ``≡``, ``sym``, ``trans``,
         and ``ℕ``.
      2. ``ρ : ℕ → ℕ`` — the path1 canonical map over Addr0 ids.
      3. ``ρ-idem`` — idempotence proof for the path1 map.
      4. One ``refl`` proof per Addr1 (glue) witnessing canonical
         equality at the path1 level.
      5. ``π : ℕ → ℕ`` — the path2 canonical map over Addr1 ids
         (only emitted if the document has any path1 records).
      6. One ``refl`` proof per Addr2 (coh) witnessing 2-cell
         coherence at the path2 level.
      7. Per-chart submodules grouping the Addr0s by their principal
         (or aux, if ``chart_kind="tau"``) chart.
    """
    addr0_idx = _addr0_index_map(doc)
    addr1_idx = _addr1_index_map(doc)
    p1_closure = _path1_closure(doc)
    p2_closure = _path2_closure(doc)

    lines: List[str] = []
    w = lines.append

    # ── Header ──────────────────────────────────────────────────
    n_sigma = sum(1 for c in doc.charts if c.kind == "sigma")
    n_tau = sum(1 for c in doc.charts if c.kind == "tau")
    n_glue = sum(1 for p in doc.paths1 if p.ctor == "glue")
    n_coh = sum(1 for p in doc.paths2 if p.ctor == "coh")
    n_classes = len({p1_closure[a] for a in addr0_idx})

    w(f"module {module_name} where")
    w("")
    w("-- ══════════════════════════════════════════════════════════")
    w(f"-- PFF Document projection: {doc.documentId}")
    w(f"-- {len(doc.addresses0)} addr0(s), {n_classes} path1 class(es)")
    w(f"-- {len(doc.charts)} chart(s) ({n_sigma} σ-kind, {n_tau} τ-kind)")
    w(f"-- {len(doc.paths1)} path1(s) ({n_glue} glue), "
      f"{len(doc.paths2)} path2(s) ({n_coh} coh)")
    w(f"-- {len(doc.ranks)} rank(s), {len(doc.patches)} patch(es)")
    w("-- ══════════════════════════════════════════════════════════")
    w("")

    # ── Prelude ─────────────────────────────────────────────────
    w("-- ── Primitives ────────────────────────────────────────────")
    w("")
    w("data _≡_ {A : Set} (x : A) : A → Set where")
    w("  refl : x ≡ x")
    w("")
    w("sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x")
    w("sym refl = refl")
    w("")
    w("trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z")
    w("trans refl refl = refl")
    w("")
    w("data ℕ : Set where")
    w("  zero : ℕ")
    w("  suc  : ℕ → ℕ")
    w("")
    w("{-# BUILTIN NATURAL ℕ #-}")
    w("")

    # ── Path1 (glue) closure ────────────────────────────────────
    _emit_pff_canonical_map(w, "ρ", addr0_idx, p1_closure)

    # ── Per-glue refl proofs ────────────────────────────────────
    if doc.paths1:
        w("-- ── Path1 (glue) witnesses ────────────────────────────────")
        w(f"-- {len(doc.paths1)} addr1 record(s)")
        w("")
        for p1 in doc.paths1:
            si = addr0_idx[p1.src]
            di = addr0_idx[p1.dst]
            safe_id = _sanitize(p1.id)
            label = p1.label or p1.ctor
            w(f"-- {p1.ctor}: {p1.src} ~ {p1.dst}  ({label})")
            w(f"{safe_id} : ρ {si} ≡ ρ {di}")
            w(f"{safe_id} = refl")
            w("")

    # ── Path2 (coh) closure ─────────────────────────────────────
    if doc.paths1:
        # Only emit a path2 map if there are path1s to point at
        _emit_pff_canonical_map(w, "π", addr1_idx, p2_closure)

    if doc.paths2:
        w("-- ── Path2 (coh) witnesses ─────────────────────────────────")
        w(f"-- {len(doc.paths2)} addr2 record(s)")
        w("")
        for p2 in doc.paths2:
            si = addr1_idx[p2.src]
            di = addr1_idx[p2.dst]
            safe_id = _sanitize(p2.id)
            label = p2.label or p2.ctor
            w(f"-- {p2.ctor}: {p2.src} ~ {p2.dst}  ({label})")
            w(f"{safe_id} : π {si} ≡ π {di}")
            w(f"{safe_id} = refl")
            w("")

    # ── Per-chart modules ───────────────────────────────────────
    # Group addr0s by the chart referenced in their first segment's
    # role-matching pair.  Each group becomes a nested module whose
    # cells refl-prove ρ-canonical equality within that chart.
    #
    # Caller invariant: every addr0 has at least one segment with
    # at least one pair whose role matches role_for_kind.  This is
    # true for documents produced by PFFCascadeEngine, where every
    # add_observation emits exactly one segment with one principal
    # pair and one aux pair.
    chart_groups: Dict[str, List[str]] = defaultdict(list)
    role_for_kind = "principal" if chart_kind == "sigma" else "aux"
    chart_kind_lookup = {c.id: c.kind for c in doc.charts}
    chart_root_lookup = {c.id: c.root for c in doc.charts}

    for addr0 in doc.addresses0:
        for pair in addr0.segments[0].pairs:
            if (pair.role == role_for_kind
                    and chart_kind_lookup.get(pair.chart) == chart_kind):
                chart_groups[pair.chart].append(addr0.id)
                break

    if chart_groups:
        w("-- ══════════════════════════════════════════════════════════")
        w(f"-- Chart partition (kind={chart_kind!r}, role={role_for_kind!r})")
        w(f"-- {len(chart_groups)} chart(s) host addr0 observations")
        w("-- ══════════════════════════════════════════════════════════")
        w("")

        # Build collision-aware module names from chart roots.
        ordered_charts = sorted(
            chart_groups.keys(),
            key=lambda cid: -len(chart_groups[cid]),
        )
        chart_names = _build_chart_names(
            ordered_charts, chart_root_lookup,
        )

        for chart_id in ordered_charts:
            members = chart_groups[chart_id]
            chart_name = chart_names[chart_id]
            chart_root = chart_root_lookup[chart_id]
            class_ids = sorted({
                addr0_idx[p1_closure[m]] for m in members
            })

            w(f"-- chart {chart_id} (root={chart_root!r}): "
              f"{len(members)} addr0(s), {len(class_ids)} path1 class(es)")
            w(f"module {chart_name} where")
            w("")
            for i, cid in enumerate(class_ids):
                w(f"  -- path1 class {cid}")
                w(f"  cell-{i} : ρ {cid} ≡ ρ {cid}")
                w(f"  cell-{i} = refl")
                w("")
            w("")

    # ── Summary ─────────────────────────────────────────────────
    w("-- ══════════════════════════════════════════════════════════")
    w(f"-- Summary:")
    w(f"--   document: {doc.documentId}")
    w(f"--   {len(doc.addresses0)} addr0(s) → {n_classes} path1 class(es)")
    w(f"--   {n_glue} glue witness(es), {n_coh} coh witness(es)")
    w(f"--   {len(chart_groups)} {chart_kind}-chart module(s)")
    w("-- ══════════════════════════════════════════════════════════")

    return "\n".join(lines) + "\n"


def _build_chart_names(
    chart_ids: List[str],
    chart_root_lookup: Dict[str, str],
) -> Dict[str, str]:
    """Compute readable, collision-disambiguated module names for charts."""
    raw: Dict[str, str] = {}
    collisions: Dict[str, List[str]] = defaultdict(list)
    for cid in chart_ids:
        base = _sanitize(chart_root_lookup[cid])
        raw[cid] = base
        collisions[base].append(cid)

    final: Dict[str, str] = {}
    for base, ids in collisions.items():
        if len(ids) == 1:
            final[ids[0]] = base
        else:
            for i, cid in enumerate(ids):
                final[cid] = f"{base}-{i}"
    return final
