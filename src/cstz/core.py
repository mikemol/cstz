"""Three-fiber SPPF engine.

The core data structures and streaming η-refinement engine.
Language-agnostic: classifiers (Python AST, bitstream, tree-sitter, etc.)
produce (ast_type, params, dep_type, kappa_tag, children) tuples and
feed them to SPPF._ingest_node().

Three fibers:
  σ (syntax)      — what it looks like structurally
  τ (type)        — what it carries (context, dependent type)
  κ (categorical) — what it does (universal construction)
"""

from __future__ import annotations

from collections import defaultdict, Counter
from typing import Any, Iterator, Optional


# ── Union-Find ───────────────────────────────────────────────────────

class UnionFind:
    """Weighted union-find with path compression."""
    __slots__ = ('_parent', '_rank')

    def __init__(self) -> None:
        self._parent: dict[Any, Any] = {}
        self._rank: dict[Any, int] = {}

    def make(self, x: Any) -> None:
        if x not in self._parent:
            self._parent[x] = x
            self._rank[x] = 0

    def find(self, x: Any) -> Any:
        r = x
        while self._parent[r] != r:
            r = self._parent[r]
        # Path compression
        while self._parent[x] != r:
            self._parent[x], x = r, self._parent[x]
        return r

    def union(self, a: Any, b: Any) -> Any:
        """Merge classes of a and b. Returns canonical representative."""
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return ra
        if self._rank[ra] < self._rank[rb]:
            ra, rb = rb, ra
        self._parent[rb] = ra
        if self._rank[ra] == self._rank[rb]:
            self._rank[ra] += 1
        return ra

    def __contains__(self, x: object) -> bool:
        return x in self._parent

    def __iter__(self) -> Iterator[Any]:
        return iter(self._parent)

    def __len__(self) -> int:
        return len(self._parent)


# ── SPPF data structures ────────────────────────────────────────────

class FiberClass:
    """A single equivalence class in one fiber."""
    __slots__ = ('id', 'signature', 'node_indices', 'child_ids')

    def __init__(self, fid: int, signature: tuple[Any, ...],
                 child_ids: tuple[int, ...]) -> None:
        self.id: int = fid
        self.signature: tuple[Any, ...] = signature
        self.child_ids: tuple[int, ...] = child_ids
        self.node_indices: list[int] = []

    def __repr__(self) -> str:
        return f"FiberClass({self.id}, {len(self.node_indices)} nodes)"


class Fiber:
    """One fibration of the SPPF (σ, τ, or κ)."""

    def __init__(self, name: str) -> None:
        self.name: str = name
        self.classes: dict[int, FiberClass] = {}
        self._registry: dict[tuple[Any, ...], int] = {}
        self._counter: int = 0
        self.uf: UnionFind = UnionFind()

    def _assign(self, signature: tuple[Any, ...],
                child_ids: tuple[int, ...], node_index: int) -> int:
        if signature in self._registry:
            fid = self._registry[signature]
        else:
            fid = self._counter
            self._counter += 1
            self._registry[signature] = fid
            self.classes[fid] = FiberClass(fid, signature, child_ids)
            self.uf.make(fid)
        self.classes[fid].node_indices.append(node_index)
        return fid

    def canonical(self, fid: int) -> int:
        """Resolve through union-find to canonical representative."""
        return self.uf.find(fid)

    def merge(self, a: int, b: int) -> int:
        """Merge two fiber classes. Returns canonical id."""
        ra, rb = self.uf.find(a), self.uf.find(b)
        if ra == rb:
            return ra
        winner: int = self.uf.union(ra, rb)
        loser = rb if winner == ra else ra
        # Merge node lists into winner
        self.classes[winner].node_indices.extend(self.classes[loser].node_indices)
        return winner

    def canonical_classes(self) -> Iterator[int]:
        """Iterate only canonical (non-merged) class ids."""
        seen: set[int] = set()
        for fid in self.classes:
            canon = self.uf.find(fid)
            if canon not in seen:
                seen.add(canon)
                yield canon

    def __len__(self) -> int:
        return sum(1 for _ in self.canonical_classes())

    def __getitem__(self, fid: int) -> FiberClass:
        return self.classes[self.uf.find(fid)]

    def __iter__(self) -> Iterator[int]:
        return self.canonical_classes()

    def __repr__(self) -> str:
        return f"Fiber({self.name!r}, {len(self)} classes)"


class SPPF:
    """Shared Packed Parse Forest with three-fiber geometry.

    Each node has coordinates (σ_id, τ_id, κ_id) in the product
    of three fibrations. The wedge product σ ∧ τ ∧ κ is the set of
    occupied cells — the maximally shared representation.

    Attributes:
        sigma: Fiber — structural (syntax) equivalence classes
        tau: Fiber — dependent type equivalence classes
        kappa: Fiber — categorical construction equivalence classes
        nodes: list — per-node records
    """

    def __init__(self) -> None:
        self.sigma: Fiber = Fiber('sigma')
        self.tau: Fiber = Fiber('tau')
        self.kappa: Fiber = Fiber('kappa')
        self.nodes: list[dict[str, Any]] = []

        # Streaming η-detection index.
        self._tau_structural: dict[
            tuple[str, tuple[int, ...]], dict[Optional[str], int]
        ] = {}
        self._tau_structural_by_child: defaultdict[
            int, set[tuple[str, tuple[int, ...]]]
        ] = defaultdict(set)
        self._tau_structural_by_variant: defaultdict[
            Optional[str], set[tuple[str, tuple[int, ...]]]
        ] = defaultdict(set)
        self._eta_abstractions: dict[str, str] = {}
        self._eta_uf: UnionFind = UnionFind()
        self._eta_count: int = 0
        self._eta_tower: list[tuple[int, list[Any], str]] = []

        # Recursive cleavage: multi-level residue tracking.
        self._residue_sets: defaultdict[int, set[Optional[str]]] = defaultdict(set)
        self._cleavage_levels: list[dict[Any, Any]] = []
        self._cleavage_fibers: list[Fiber] = []
        self._cleavage_ghost_count: int = 0

        # Per-cell observation counters with downward projection.
        self._cell_obs: defaultdict[int, defaultdict[Any, int]] = defaultdict(
            lambda: defaultdict(int))
        self._cell_contents: defaultdict[tuple[int, Any], set[Any]] = defaultdict(set)

    # ── Cell observation ─────────────────────────────────────────

    def _observe_cell(self, level: int, cell_id: Any,
                      contained_ids: Optional[list[Any]] = None) -> None:
        """Record observation of a k-cell and project +1 to each
        contained (k-1)-cell, recursively down to 0-cells."""
        self._cell_obs[level][cell_id] += 1
        if contained_ids:
            key = (level, cell_id)
            for cid in contained_ids:
                self._cell_contents[key].add(cid)
        if level > 0:
            # Recursion terminates by construction: _cell_contents[(level, id)]
            # only holds IDs recorded at level-1; level strictly decreases to 0
            # and cycles are impossible. (Corresponds to P3 well-founded induction.)
            key = (level, cell_id)
            for child_id in self._cell_contents.get(key, ()):
                self._observe_cell(level - 1, child_id)

    # ── Cleavage ─────────────────────────────────────────────────

    def _process_cleavage(self, merged_tid: int, ast_type: str,
                          trigger_node_index: int) -> None:
        """Process cleavage recursively after a τ-merge."""
        canon_tid = self.tau.canonical(merged_tid)
        raw_residue = self._residue_sets.get(canon_tid, set())
        residue_sig = tuple(sorted(
            self._resolve_type(t) or t for t in raw_residue
        ))

        if len(residue_sig) < 2:
            return

        current_sig = residue_sig
        current_context = ast_type
        level = 0

        while True:
            while level >= len(self._cleavage_levels):
                self._cleavage_levels.append({})
                fiber = Fiber(f'cleavage_{len(self._cleavage_fibers)}')
                self._cleavage_fibers.append(fiber)

            level_index = self._cleavage_levels[level]
            level_fiber = self._cleavage_fibers[level]
            cleavage_key = (current_context, current_sig)

            if cleavage_key in level_index:
                existing = level_index[cleavage_key]
                parent_key = canon_tid

                if parent_key not in existing:
                    existing[parent_key] = canon_tid

                    if len(existing) >= 2:
                        # κ-coverability filter using κ-tag
                        ktag_sets: set[frozenset[Any]] = set()
                        for tid_val in existing.values():
                            cid = self.tau.canonical(tid_val)
                            if cid in self.tau.classes:  # pragma: no branch
                                ks = frozenset(
                                    self.nodes[ni].get('kappa_tag')
                                    for ni in self.tau.classes[cid].node_indices
                                    if ni < len(self.nodes)
                                )
                                ktag_sets.add(ks)

                        is_ghost = len(ktag_sets) <= 1
                        if is_ghost:
                            self._cleavage_ghost_count += 1
                            tag = f"ghost-cleavage-L{level}:{current_sig[:3]}"
                        else:
                            tag = f"η-cleavage-L{level}:{current_sig[:3]}"

                        self._eta_tower.append((
                            trigger_node_index, list(existing.keys()), tag
                        ))

                        # Cell observation
                        cell_level = 3 + level
                        contained_2cells: set[Any] = set()
                        for tid_val in existing.values():
                            cid = self.tau.canonical(tid_val)
                            for raw_t in self._residue_sets.get(cid, ()):
                                abs_name = self._eta_abstractions.get(raw_t)
                                if abs_name:
                                    contained_2cells.add(
                                        self._eta_uf.find(abs_name)
                                        if abs_name in self._eta_uf
                                        else abs_name)
                        self._observe_cell(
                            cell_level, cleavage_key,
                            list(contained_2cells) if contained_2cells else None)

                        # Annotate nodes
                        cleavage_class_id = level_fiber._counter
                        level_fiber._counter += 1
                        for tid_val in existing.values():
                            cid = self.tau.canonical(tid_val)
                            for ni in self.tau.classes[cid].node_indices:
                                if ni >= len(self.nodes):
                                    continue
                                node = self.nodes[ni]
                                # First-writer-wins: informational annotation
                                # only; does not affect any merge logic.
                                if f'cleavage_{level}' not in node:
                                    node[f'cleavage_{level}'] = cleavage_class_id

                        next_residue = tuple(sorted(set(
                            self.tau.canonical(t) for t in existing.values()
                        )))
                        if len(next_residue) >= 2:
                            current_sig = next_residue
                            current_context = f"cleavage_{level}"
                            level += 1
                            continue
                break  # pragma: no cover — coverage.py while-True tracing quirk
            else:
                level_index[cleavage_key] = {canon_tid: canon_tid}
                break

    # ── Residue tracking ─────────────────────────────────────────

    def _update_residue(self, tau_id: int, raw_dep_type: Optional[str]) -> None:
        canon = self.tau.canonical(tau_id)
        if raw_dep_type is not None:
            self._residue_sets[canon].add(raw_dep_type)

    def _merge_residue_sets(self, winner: int, loser: int) -> None:
        w = self.tau.canonical(winner)
        l = self.tau.canonical(loser)
        if l in self._residue_sets:
            self._residue_sets[w].update(self._residue_sets[l])

    # ── Abstraction cascade ──────────────────────────────────────

    def _cascade_abstraction_merge(self, merged_names: set[str],
                                   trigger_node_index: int) -> set[int]:
        """After η-union-find merges abstraction names, recheck structural
        keys whose variants are keyed by those names.

        Returns a set of tau IDs whose structural-key parents need
        cascading (replacing the former recursive _cascade_eta call).
        """
        deferred_tau_ids: set[int] = set()
        affected_keys: set[tuple[str, tuple[int, ...]]] = set()
        for name in merged_names:
            affected_keys.update(self._tau_structural_by_variant.get(name, set()))

        for struct_key in affected_keys:
            if struct_key not in self._tau_structural:
                continue
            variants = self._tau_structural[struct_key]

            rekeyed: dict[Optional[str], int] = {}
            merges: list[tuple[Any, Optional[str], int]] = []
            for dt, tid in list(variants.items()):
                resolved = self._resolve_type(dt)
                canon_tid = self.tau.canonical(tid)
                if resolved in rekeyed:
                    existing_canon = self.tau.canonical(rekeyed[resolved])
                    if existing_canon != canon_tid:
                        self._merge_residue_sets(existing_canon, canon_tid)
                        winner = self.tau.merge(existing_canon, canon_tid)
                        rekeyed[resolved] = winner
                        merges.append((dt, resolved, winner))
                else:
                    rekeyed[resolved] = canon_tid

            if merges:
                self._tau_structural[struct_key] = rekeyed
                for dt in variants:
                    self._tau_structural_by_variant[dt].discard(struct_key)
                for dt in rekeyed:
                    self._tau_structural_by_variant[dt].add(struct_key)

                for dt, resolved, winner in merges:
                    self._eta_count += 1
                    self._eta_tower.append((
                        trigger_node_index, [dt, resolved],
                        f"η-transitive:{resolved}"
                    ))
                    final = self.tau.canonical(winner)
                    ast_t = (struct_key[0] if isinstance(struct_key[0], str)
                             else str(struct_key[0]))
                    self._process_cleavage(final, ast_t, trigger_node_index)
                    deferred_tau_ids.add(final)

        return deferred_tau_ids

    def _resolve_type(self, dep_type: Optional[str]) -> Optional[str]:
        """Resolve a dep_type through the full abstraction chain."""
        if dep_type is None:
            return None
        abs_name = self._eta_abstractions.get(dep_type, dep_type)
        if abs_name in self._eta_uf:
            return self._eta_uf.find(abs_name)
        return abs_name

    def _recanon_structural_key(
        self, old_key: tuple[str, tuple[int, ...]]
    ) -> tuple[tuple[str, tuple[int, ...]], bool]:
        ast_type, child_taus = old_key
        new_children = tuple(self.tau.canonical(c) for c in child_taus)
        new_key = (ast_type, new_children)
        return new_key, new_key != old_key

    def _seed_worklist(self, tau_ids: set[int],
                       target: set[tuple[str, tuple[int, ...]]]) -> None:
        """Add structural-key parents of the given tau IDs to *target*."""
        for tid in tau_ids:
            target.update(self._tau_structural_by_child.get(tid, set()))
            canon = self.tau.canonical(tid)
            if canon != tid:
                target.update(self._tau_structural_by_child.get(canon, set()))

    def _cascade_eta(self, merged_tau_ids: set[int],
                     trigger_node_index: int) -> None:
        """Cascade after τ-merges: re-canonicalize structural keys
        whose children were merged, revealing higher-order transformations."""
        worklist: set[tuple[str, tuple[int, ...]]] = set()
        self._seed_worklist(merged_tau_ids, worklist)

        while worklist:
            next_worklist: set[tuple[str, tuple[int, ...]]] = set()
            keys_to_reindex = list(worklist)
            worklist = set()

            for old_key in keys_to_reindex:
                if old_key not in self._tau_structural:
                    continue
                variants = self._tau_structural[old_key]
                new_key, changed = self._recanon_structural_key(old_key)

                if not changed:
                    rekeyed: dict[Optional[str], int] = {}
                    merges_here: list[tuple[Any, Optional[str]]] = []
                    for dt, tid in variants.items():
                        abs_dt = self._resolve_type(dt)
                        canon_tid = self.tau.canonical(tid)
                        if abs_dt in rekeyed:
                            existing_canon = self.tau.canonical(rekeyed[abs_dt])
                            if existing_canon != canon_tid:
                                self._merge_residue_sets(existing_canon, canon_tid)
                                winner = self.tau.merge(existing_canon, canon_tid)
                                rekeyed[abs_dt] = winner
                                merges_here.append((dt, abs_dt))
                        else:
                            rekeyed[abs_dt] = canon_tid
                    if merges_here:  # pragma: no branch
                        self._eta_count += len(merges_here)
                        self._eta_tower.append((
                            trigger_node_index,
                            [m[0] for m in merges_here],
                            "η-cascade:dep_abstract"
                        ))
                        self._tau_structural[old_key] = rekeyed
                        for tid in rekeyed.values():
                            canon = self.tau.canonical(tid)
                            next_worklist.update(
                                self._tau_structural_by_child.get(canon, set()))
                            ast_t = (old_key[0] if isinstance(old_key[0], str)
                                     else str(old_key[0]))
                            self._process_cleavage(
                                canon, ast_t, trigger_node_index)
                    continue

                del self._tau_structural[old_key]
                _, old_children = old_key
                for c in old_children:
                    self._tau_structural_by_child.get(c, set()).discard(old_key)

                if new_key in self._tau_structural:
                    target = self._tau_structural[new_key]
                    for dt, tid in variants.items():
                        abs_dt = self._resolve_type(dt)
                        canon_tid = self.tau.canonical(tid)
                        if abs_dt in target:
                            existing_canon = self.tau.canonical(target[abs_dt])
                            if existing_canon != canon_tid:
                                self._merge_residue_sets(
                                    existing_canon, canon_tid)
                                winner = self.tau.merge(
                                    existing_canon, canon_tid)
                                target[abs_dt] = winner
                                self._eta_count += 1
                                self._eta_tower.append((
                                    trigger_node_index,
                                    [abs_dt], "η-cascade:key_collision"
                                ))
                                winner_canon = self.tau.canonical(winner)
                                next_worklist.update(
                                    self._tau_structural_by_child.get(
                                        winner_canon, set()))
                                ast_t = (new_key[0]
                                         if isinstance(new_key[0], str)
                                         else str(new_key[0]))
                                self._process_cleavage(
                                    winner_canon, ast_t, trigger_node_index)
                        else:
                            target[abs_dt] = canon_tid
                else:
                    # Bug fix: use _resolve_type (not bare
                    # _eta_abstractions.get) so the union-find chain
                    # is fully resolved, and handle collisions that
                    # the full resolution may reveal.
                    rekeyed_new: dict[Optional[str], int] = {}
                    for dt, tid in variants.items():
                        resolved = self._resolve_type(dt)
                        canon_tid = self.tau.canonical(tid)
                        if resolved in rekeyed_new:  # pragma: no branch
                            existing_canon = self.tau.canonical(
                                rekeyed_new[resolved])
                            if existing_canon != canon_tid:  # pragma: no branch
                                self._merge_residue_sets(
                                    existing_canon, canon_tid)
                                winner = self.tau.merge(
                                    existing_canon, canon_tid)
                                rekeyed_new[resolved] = winner
                                self._eta_count += 1
                                self._eta_tower.append((
                                    trigger_node_index,
                                    [resolved],
                                    "η-cascade:rekey_collision"
                                ))
                                winner_canon = self.tau.canonical(winner)
                                next_worklist.update(
                                    self._tau_structural_by_child.get(
                                        winner_canon, set()))
                                ast_t = (new_key[0]
                                         if isinstance(new_key[0], str)
                                         else str(new_key[0]))
                                self._process_cleavage(
                                    winner_canon, ast_t,
                                    trigger_node_index)
                        else:
                            rekeyed_new[resolved] = canon_tid
                    self._tau_structural[new_key] = rekeyed_new
                    _, new_children = new_key
                    for c in new_children:
                        self._tau_structural_by_child[c].add(new_key)
                    for rv in rekeyed_new:
                        self._tau_structural_by_variant[rv].add(new_key)

                merged_variants = self._tau_structural.get(new_key, {})
                canon_tids: dict[int, Any] = {}
                for dt, tid in list(merged_variants.items()):
                    ct = self.tau.canonical(tid)
                    if ct not in canon_tids:
                        canon_tids[ct] = dt

                if len(canon_tids) > 1:
                    all_tids = list(canon_tids.keys())
                    all_types = list(merged_variants.keys())
                    self._eta_count += 1
                    eta_name = f"∀η².{all_types[0]}"
                    self._eta_uf.make(eta_name)
                    unified_names_2: set[Any] = {eta_name}
                    for dt in all_types:
                        resolved = self._resolve_type(dt)
                        if resolved != eta_name:  # pragma: no branch
                            if resolved in self._eta_uf:
                                self._eta_uf.union(eta_name, resolved)
                                unified_names_2.add(resolved)
                            self._eta_abstractions[dt] = eta_name
                    if len(unified_names_2) > 1:
                        deferred = self._cascade_abstraction_merge(
                            unified_names_2, trigger_node_index)
                        self._seed_worklist(deferred, next_worklist)
                    canonical = all_tids[0]
                    for other in all_tids[1:]:
                        c_can = self.tau.canonical(canonical)
                        o_can = self.tau.canonical(other)
                        if o_can != c_can:
                            self._merge_residue_sets(c_can, o_can)
                            canonical = self.tau.merge(c_can, o_can)
                    self._eta_tower.append(
                        (trigger_node_index, all_types, eta_name))
                    final_canon = self.tau.canonical(canonical)
                    next_worklist.update(
                        self._tau_structural_by_child.get(
                            final_canon, set()))
                    ast_t = (new_key[0] if isinstance(new_key[0], str)
                             else str(new_key[0]))
                    self._process_cleavage(
                        final_canon, ast_t, trigger_node_index)

            worklist = next_worklist

    # ── Node ingestion ───────────────────────────────────────────

    def _ingest_node(self, ast_type: str, params: tuple[tuple[str, Any], ...],
                     dep_type: Optional[str], kappa_tag: str,
                     child_sigmas: tuple[int, ...],
                     child_taus: tuple[int, ...],
                     child_kappas: tuple[int, ...],
                     line: int, filename: str
                     ) -> tuple[int, int, int, int]:
        """Ingest a single node with streaming η-refinement.

        Returns (sigma_id, tau_id, kappa_id, node_index).
        """
        node_index = len(self.nodes)

        sigma_sig = (ast_type, params, child_sigmas)
        kappa_sig = (kappa_tag, child_kappas)
        sid = self.sigma._assign(sigma_sig, child_sigmas, node_index)
        kid = self.kappa._assign(kappa_sig, child_kappas, node_index)

        canon_child_taus = tuple(self.tau.canonical(ct) for ct in child_taus)
        abs_type = self._resolve_type(dep_type)

        tau_sig: tuple[str, Optional[str], tuple[int, ...]] = (
            ast_type, abs_type, canon_child_taus)
        tid = self.tau._assign(tau_sig, canon_child_taus, node_index)

        # ── Streaming η-detection ──
        struct_key: tuple[str, tuple[int, ...]] = (ast_type, canon_child_taus)

        if abs_type is not None and struct_key in self._tau_structural:
            existing = self._tau_structural[struct_key]
            canon_tid = self.tau.canonical(tid)

            if abs_type not in existing:
                should_merge = any(
                    self.tau.canonical(other_tid) != canon_tid
                    for other_tid in existing.values()
                )

                if should_merge:
                    all_tids = [self.tau.canonical(t) for t in existing.values()]
                    all_tids.append(canon_tid)
                    all_types = list(existing.keys()) + [abs_type]

                    self._eta_count += 1
                    eta_name = f"∀η.{ast_type}.{all_types[0]}"
                    self._eta_uf.make(eta_name)

                    unified_names: set[Any] = {eta_name}
                    for dt in all_types:
                        resolved = self._resolve_type(dt)
                        if resolved != eta_name:
                            if resolved in self._eta_uf:
                                self._eta_uf.union(eta_name, resolved)
                                unified_names.add(resolved)
                            self._eta_abstractions[dt] = eta_name

                    canonical = all_tids[0]
                    for other in all_tids[1:]:
                        c = self.tau.canonical(other)
                        canon_c = self.tau.canonical(canonical)
                        if c != canon_c:
                            self._merge_residue_sets(canon_c, c)
                            canonical = self.tau.merge(canon_c, c)

                    self._eta_tower.append(
                        (node_index, all_types, eta_name))
                    tid = self.tau.canonical(canonical)

                    self._observe_cell(2, eta_name,
                        [self.tau.canonical(t) for t in all_tids])

                    self._update_residue(tid, dep_type)

                    deferred_from_abs: set[int] = set()
                    if len(unified_names) > 1:
                        deferred_from_abs = self._cascade_abstraction_merge(
                            unified_names, node_index)

                    merged_set = set(self.tau.canonical(t) for t in all_tids)
                    merged_set.add(self.tau.canonical(canonical))
                    merged_set.update(deferred_from_abs)
                    self._cascade_eta(merged_set, node_index)

                    self._process_cleavage(tid, ast_type, node_index)

                existing[abs_type] = tid
                self._tau_structural_by_variant[abs_type].add(struct_key)
            else:
                tid = self.tau.canonical(tid)
        elif abs_type is not None:
            self._tau_structural[struct_key] = {abs_type: tid}
            self._tau_structural_by_variant[abs_type].add(struct_key)
            for c in canon_child_taus:
                self._tau_structural_by_child[c].add(struct_key)

        self._update_residue(tid, dep_type)

        self.nodes.append({
            'ast_type': ast_type,
            'params': params,
            'dep_type': abs_type,
            'dep_type_raw': dep_type,
            'kappa_tag': kappa_tag,
            'sigma': sid,
            'tau': self.tau.canonical(tid),
            'kappa': kid,
            'line': line,
            'file': filename,
        })

        final_tid = self.tau.canonical(tid)
        self._cell_contents[(1, final_tid)].add(node_index)

        return (sid, final_tid, kid, node_index)

    # ── Projections and queries ──────────────────────────────────

    @property
    def node_count(self) -> int:
        return len(self.nodes)

    def _resolve(self, node: dict[str, Any], fiber_name: str) -> int:
        fid: int = node[fiber_name]
        fiber: Fiber = getattr(self, fiber_name)
        return fiber.canonical(fid)

    def wedge(self) -> dict[tuple[int, int, int], list[int]]:
        """Full wedge product σ ∧ τ ∧ κ → {(σ,τ,κ): [node_indices]}"""
        cells: defaultdict[tuple[int, int, int], list[int]] = defaultdict(list)
        for i, n in enumerate(self.nodes):
            cells[(self._resolve(n, 'sigma'),
                   self._resolve(n, 'tau'),
                   self._resolve(n, 'kappa'))].append(i)
        return dict(cells)

    def wedge_2(self, fiber_a: str,
                fiber_b: str) -> dict[tuple[int, int], list[int]]:
        """Two-fiber wedge product → {(a,b): [node_indices]}"""
        cells: defaultdict[tuple[int, int], list[int]] = defaultdict(list)
        for i, n in enumerate(self.nodes):
            cells[(self._resolve(n, fiber_a),
                   self._resolve(n, fiber_b))].append(i)
        return dict(cells)

    def rotate(self, from_fiber: str,
               to_fiber: str) -> dict[int, dict[int, int]]:
        """Project each class in from_fiber through to_fiber.
        Returns {from_id: {to_id: count}}"""
        result: defaultdict[int, Counter[int]] = defaultdict(Counter)
        for n in self.nodes:
            result[self._resolve(n, from_fiber)][
                self._resolve(n, to_fiber)] += 1
        return {k: dict(v) for k, v in result.items()}

    def rank(self, fiber: str, fid: int, target_fiber: str) -> int:
        """Rank of a class: how many target classes it maps to."""
        targets: set[int] = set()
        fiber_obj: Fiber = getattr(self, fiber)
        canon_fid = fiber_obj.canonical(fid)
        for node_idx in fiber_obj.classes[canon_fid].node_indices:
            targets.add(self._resolve(self.nodes[node_idx], target_fiber))
        return len(targets)

    def rank_distribution(self, fiber: str,
                          target_fiber: str) -> Counter[int]:
        """Distribution of ranks across all classes in a fiber."""
        dist: Counter[int] = Counter()
        fiber_obj: Fiber = getattr(self, fiber)
        for fid in fiber_obj:
            dist[self.rank(fiber, fid, target_fiber)] += 1
        return dist

    def hybrid(self) -> tuple[set[tuple[str, int]], Counter[str]]:
        """Per-node best fiber: whichever gives the largest class."""
        winners: Counter[str] = Counter()
        classes: set[tuple[str, int]] = set()
        for n in self.nodes:
            s_id = self._resolve(n, 'sigma')
            t_id = self._resolve(n, 'tau')
            k_id = self._resolve(n, 'kappa')
            sizes: dict[str, int] = {
                'sigma': len(self.sigma.classes[s_id].node_indices),
                'tau': len(self.tau.classes[t_id].node_indices),
                'kappa': len(self.kappa.classes[k_id].node_indices),
            }
            # Tie-breaking: sigma wins ties (dict insertion order is always
            # sigma → tau → kappa; Python 3.7+ preserves insertion order).
            best_fiber = max(sizes, key=sizes.get)  # type: ignore[arg-type]
            winners[best_fiber] += 1
            ids = {'sigma': s_id, 'tau': t_id, 'kappa': k_id}
            classes.add((best_fiber, ids[best_fiber]))
        return classes, winners

    def natural_transformations(
        self, fiber: str
    ) -> list[tuple[int, dict[str, int]]]:
        """Find classes that map to multiple classes in all other fibers."""
        fiber_obj: Fiber = getattr(self, fiber)
        other_names = [f for f in ('sigma', 'tau', 'kappa') if f != fiber]
        results: list[tuple[int, dict[str, int]]] = []
        for fid in fiber_obj:
            ranks: dict[str, int] = {}
            for other in other_names:
                r = self.rank(fiber, fid, other)
                if r > 1:
                    ranks[other] = r
            if ranks:
                results.append((fid, ranks))
        results.sort(key=lambda x: -max(x[1].values()))
        return results

    def residue(self, tau_id: int) -> dict[Optional[str], list[int]]:
        """Compute the residue of a τ-class."""
        fiber_class = self.tau[tau_id]
        by_raw: defaultdict[Any, list[int]] = defaultdict(list)
        for ni in fiber_class.node_indices:
            raw = self.nodes[ni].get('dep_type_raw')
            by_raw[raw].append(ni)
        return dict(by_raw)

    def cleavage(self) -> list[tuple[int, dict[Optional[str], int], int]]:
        """All cleavage planes: τ-classes with residue rank > 1."""
        result: list[tuple[int, dict[Optional[str], int], int]] = []
        for tid in self.tau:
            res = self.residue(tid)
            if len(res) > 1:
                counts = {k: len(v) for k, v in res.items()}
                total = sum(counts.values())
                result.append((tid, counts, total))
        result.sort(key=lambda x: -x[2])
        return result

    def __repr__(self) -> str:
        hc, hw = self.hybrid()
        return (
            f"SPPF({self.node_count} nodes, "
            f"σ={len(self.sigma)}, τ={len(self.tau)}, κ={len(self.kappa)}, "
            f"hybrid={len(hc)})"
        )

    def summary(self) -> str:
        """Human-readable summary of the three-fiber decomposition."""
        N = self.node_count
        if N == 0:
            return "SPPF: 0 nodes"
        S = len(self.sigma)
        T = len(self.tau)
        K = len(self.kappa)
        hc, hw = self.hybrid()
        w = self.wedge()

        lines = [
            f"SPPF: {N} nodes",
            f"",
            f"  σ (syntax):       {S:6d} classes  ({1-S/N:.1%} compression)",
            f"  τ (type):         {T:6d} classes  ({1-T/N:.1%} compression)",
            f"  κ (categorical):  {K:6d} classes  ({1-K/N:.1%} compression)",
            f"  σ∧τ∧κ (wedge):   {len(w):6d} cells   ({1-len(w)/N:.1%} compression)",
            f"  hybrid (best/node): {len(hc):5d} classes  ({1-len(hc)/N:.1%} compression)",
            f"",
            f"  Per-node winner: {dict(hw)}",
        ]

        # η summary
        cleavage_real = sum(
            1 for e in self._eta_tower
            if isinstance(e[2], str) and e[2].startswith('η-cleavage')
        )
        eta_names: set[Any] = set(self._eta_uf)
        eta_roots = (set(self._eta_uf.find(n) for n in eta_names)
                     if eta_names else set())
        transitive_merges = len(eta_names) - len(eta_roots)

        sigma_ktags: dict[int, set[Optional[str]]] = {}
        for n in self.nodes:
            sid: int = n['sigma']
            if sid not in sigma_ktags:
                sigma_ktags[sid] = set()
            sigma_ktags[sid].add(n.get('kappa_tag'))
        kappa_independent = sum(1 for v in sigma_ktags.values() if len(v) > 1)

        lines.append(f"  η first-order: {self._eta_count}")
        lines.append(
            f"  η higher-order: {transitive_merges} transitive merges "
            f"({len(eta_names)} abstractions → {len(eta_roots)} classes)"
        )
        lines.append(
            f"  η cleavage: {cleavage_real} real, "
            f"{self._cleavage_ghost_count} ghost "
            f"({len(self._cleavage_levels)} levels)"
        )
        lines.append(
            f"  κ independence: {kappa_independent}/{S} σ-classes "
            f"map to >1 κ-tag (ghost filter "
            f"{'informative' if kappa_independent > S * 0.01 else 'degenerate'})"
        )

        # Cell observations
        cell_names = {0: 'node', 1: 'τ-class', 2: 'η-merge',
                      3: 'cleavage-L0', 4: 'cleavage-L1'}
        observed_0 = len(self._cell_obs.get(0, {}))
        inert = N - observed_0
        lines.append("  cell observations (projected):")
        lines.append(f"    structurally active nodes: {observed_0} "
                     f"({observed_0/N:.1%}), inert: {inert} ({inert/N:.1%})")
        for level in sorted(self._cell_obs.keys()):
            cells = self._cell_obs[level]
            if not cells:
                continue
            name = cell_names.get(level, f'L{level}-cell')
            top_id, top_obs = max(cells.items(), key=lambda x: x[1])
            label = str(top_id)[:40]
            lines.append(f"    {level}-cell ({name}): "
                         f"{len(cells)} observed, "
                         f"peak={top_obs}× ({label})")

        # Rank summary
        for fiber in ('sigma', 'tau', 'kappa'):
            for target_fiber in ('sigma', 'tau', 'kappa'):
                if fiber == target_fiber:
                    continue
                dist = self.rank_distribution(fiber, target_fiber)
                rank1 = dist.get(1, 0)
                total = sum(dist.values())
                if total > 0:  # pragma: no branch
                    max_rank = max(dist)
                    lines.append(
                        f"  rank({fiber}→{target_fiber}): "
                        f"{rank1}/{total} unambiguous ({rank1/total:.0%}), "
                        f"max rank {max_rank}"
                    )

        return "\n".join(lines)
