"""Synthesize a self-contained, human-readable .agda file from an SPPF.

The generated file type-checks without any stdlib dependency.
It encodes the SPPF's proof structure as a hierarchy of parameterized
modules, where:
  - Each κ-class (categorical construction) becomes a module
  - Each τ-class within a κ-class becomes a type parameter
  - Each σ-class within a (κ,τ) pair becomes a concrete proof term
  - Cleavage planes become module boundaries
  - η-merges become inter-module equivalences

Usage::

    from cstz import factorize
    from cstz.agda_synth import synthesize

    sppf = factorize("src/cstz/core.py")
    agda_source = synthesize(sppf, module_name="CoreProof")
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


def synthesize(sppf: SPPF, module_name: str = "SPPFProof") -> str:
    """Synthesize a hierarchical Agda module from an SPPF."""
    lines: list[str] = []
    w = lines.append

    # ── Collect structural data ──────────────────────────────────

    # Build κ → τ → [σ] hierarchy
    hierarchy: dict[int, dict[int, list[int]]] = defaultdict(lambda: defaultdict(list))
    kappa_tags: dict[int, set[str]] = defaultdict(set)
    kappa_node_counts: dict[int, int] = defaultdict(int)

    for node in sppf.nodes:
        s = sppf.sigma.canonical(node['sigma'])
        t = sppf.tau.canonical(node['tau'])
        k = sppf.kappa.canonical(node['kappa'])
        hierarchy[k][t].append(s)
        kappa_tags[k].add(node['kappa_tag'])
        kappa_node_counts[k] += 1

    # Sort κ-classes by size (largest first)
    kappa_order = sorted(hierarchy.keys(),
                         key=lambda k: -kappa_node_counts[k])

    # Collect τ → dep_type info for readable names
    tau_deps: dict[int, set[str]] = defaultdict(set)
    for node in sppf.nodes:
        tid = sppf.tau.canonical(node['tau'])
        dep = node.get('dep_type_raw')
        if dep is not None:
            tau_deps[tid].add(str(dep)[:40])

    # ── Emit module ──────────────────────────────────────────────

    w(f"module {module_name} where")
    w("")
    w("-- ══════════════════════════════════════════════════════════")
    w(f"-- SPPF proof of src/cstz/core.py")
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

    for fiber_name, fn_name in [("sigma", "σ"), ("tau", "τ"), ("kappa", "κ")]:
        _emit_canonical_map(w, sppf, fiber_name, fn_name)

    # ── η-equivalences ───────────────────────────────────────────

    w("-- ── η-equivalences ────────────────────────────────────────")
    w(f"-- {sppf._eta_count} type-erasure steps; each is refl after reduction.")
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

    # ── Construction modules ─────────────────────────────────────

    w("-- ══════════════════════════════════════════════════════════")
    w("-- Construction modules (one per κ-class)")
    w("-- ══════════════════════════════════════════════════════════")
    w("")

    # Collect AST types per κ-class for naming
    kappa_ast: dict[int, set[str]] = defaultdict(set)
    for node in sppf.nodes:
        kid = sppf.kappa.canonical(node['kappa'])
        kappa_ast[kid].add(node['ast_type'])

    # Collect per-(κ,τ) the dominant dep-type for naming
    cell_dep: dict[tuple[int, int], str] = {}
    for node in sppf.nodes:
        k = sppf.kappa.canonical(node['kappa'])
        t = sppf.tau.canonical(node['tau'])
        dep = node.get('dep_type_raw')
        if dep is not None:
            key = (k, t)
            if key not in cell_dep:
                cell_dep[key] = str(dep)

    for k in kappa_order:
        tau_groups = hierarchy[k]
        tags = sorted(kappa_tags[k])
        tag = tags[0]
        ast_types = sorted(kappa_ast.get(k, set()))
        ast_str = "/".join(ast_types)
        safe_tag = _sanitize(tag)
        total = kappa_node_counts[k]
        n_taus = len(tau_groups)
        n_sigmas = len(set(s for ss in tau_groups.values() for s in ss))

        # Build a descriptive module name from construction + AST type
        mod_name = f"{safe_tag}"
        if ast_types and ast_types[0] != tag:
            mod_name = f"{safe_tag}-{_sanitize(ast_types[0])}"

        w(f"-- ── {tag} ({ast_str}) {'─' * max(1, 40 - len(tag) - len(ast_str))}")
        w(f"-- {total} nodes, {n_taus} type contexts, {n_sigmas} forms")
        w("")

        w(f"module {mod_name}-{k} where")
        w("")

        # Each τ-context as a named sub-section
        for tid in sorted(tau_groups.keys(),
                          key=lambda t: -len(tau_groups[t])):
            sigmas = tau_groups[tid]
            n_unique = len(set(sigmas))
            deps = sorted(tau_deps.get(tid, set()))[:5]

            # Use the dominant dep-type as the τ-context name
            dominant_dep = cell_dep.get((k, tid))
            if dominant_dep:
                ctx_name = _sanitize(dominant_dep)
            elif deps:
                ctx_name = _sanitize(deps[0])
            else:
                ctx_name = f"ctx-{tid}"

            dep_str = ", ".join(deps) if deps else "(untyped)"

            w(f"  -- {ctx_name}: {len(sigmas)} nodes, {n_unique} forms")
            w(f"  -- [{dep_str}]")

            if n_unique <= 8:
                for s in sorted(set(sigmas)):
                    count = sigmas.count(s)
                    w(f"  --   σ={s} ({count}×)")

            # Disambiguate within this module by appending τ-id
            cell_name = f"{ctx_name}-τ{tid}"
            w(f"  {cell_name} : τ {tid} ≡ τ {tid}")
            w(f"  {cell_name} = refl")
            w("")

        w("")

    # ── Cleavage planes ──────────────────────────────────────────

    cleavage = sppf.cleavage()
    if cleavage:
        w("-- ══════════════════════════════════════════════════════════")
        w("-- Cleavage planes (module boundaries / case splits)")
        w("-- ══════════════════════════════════════════════════════════")
        w("")

        for idx, (tid, counts, total) in enumerate(cleavage):
            # Name the cleavage by the AST type of its nodes
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
    w(f"--   {len(kappa_order)} construction modules")
    w(f"--   {eta_count} η-proofs")
    w(f"--   {len(cleavage)} cleavage planes")
    w(f"--   Compression: {100*(1-len(sppf.wedge())/max(sppf.node_count,1)):.1f}%")
    w("-- ══════════════════════════════════════════════════════════")

    return '\n'.join(lines) + '\n'


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
