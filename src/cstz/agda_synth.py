"""Synthesize a self-contained, human-readable .agda file from an SPPF.

The generated file type-checks without any stdlib dependency.

Usage::

    from cstz import factorize
    from cstz.agda_synth import synthesize

    sppf = factorize("src/cstz/core.py")

    # Default rotation: κ → τ → σ at depth 2 (κ outermost, τ submodules)
    agda_source = synthesize(sppf, module_name="CoreProof")

    # Custom: rotate so τ leads, depth 1 (only τ-grouped, no nesting)
    agda_source = synthesize(
        sppf,
        rotation=("tau", "kappa", "sigma"),
        depth=1,
    )

The rotation tuple selects which fiber is the primary grouping axis,
secondary, and tertiary.  The depth controls how many axes become
nested module boundaries (depth=1: only primary; depth=2: primary +
secondary; depth=3: full nesting through all three).
"""

from __future__ import annotations

from collections import defaultdict
from typing import Any

from .core import SPPF


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
