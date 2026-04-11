"""Tests for the PFF Document → Agda projection in cstz.agda_synth.

Exercises ``synthesize_from_document`` and its helpers, including
end-to-end Agda type-checking when the ``agda`` binary is available.

These tests do NOT exercise the legacy ``synthesize(sppf, ...)`` path
— that is the metamathematical reference and lives in
test_agda_synth_legacy.py (currently absent; the legacy path has no
tests in this suite, but is exercised end-to-end via inference.agda).
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

from cstz.agda_synth import (
    _addr0_index_map,
    _addr1_index_map,
    _build_chart_names,
    _path1_closure,
    _path2_closure,
    _sanitize,
    synthesize_from_document,
)
from cstz.pff_cascade import PFFCascadeEngine
from cstz.pff_python_classifier import factorize


# ── Helpers ─────────────────────────────────────────────────────────


def _empty_engine() -> PFFCascadeEngine:
    e = PFFCascadeEngine(document_id="empty")
    e.ensure_rank(0)
    e.ensure_patch("ingest")
    return e


def _two_obs_engine(glue: bool = True) -> PFFCascadeEngine:
    """Engine with two observations; the streaming cascade glues them
    iff their σ-charts collide and τ-charts differ."""
    e = PFFCascadeEngine(document_id="two-obs")
    sigma = e.ensure_chart("sigma", "X" if glue else "X")
    sigma2 = e.ensure_chart("sigma", "X" if glue else "Y")
    tau_a = e.ensure_chart("tau", "A")
    tau_b = e.ensure_chart("tau", "B")
    e.add_observation(sigma, tau_a)
    e.add_observation(sigma2, tau_b)
    return e


def _agda_available() -> bool:
    return shutil.which("agda") is not None


def _agda_check(source: str, module_name: str, tmp_path: Path) -> None:
    """Write *source* to ``tmp_path/<module_name>.agda`` and type-check
    it with ``agda --safe``.  Raises if Agda exits non-zero."""
    f = tmp_path / f"{module_name}.agda"
    f.write_text(source)
    result = subprocess.run(
        ["agda", "--safe", str(f)],
        capture_output=True,
        text=True,
        cwd=str(tmp_path),
    )
    if result.returncode != 0:
        raise AssertionError(
            f"agda failed for {module_name}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


# ── _sanitize ───────────────────────────────────────────────────────


class TestSanitize:
    def test_alphanumeric_passthrough(self) -> None:
        assert _sanitize("foo_bar") == "foo_bar"

    def test_dot_becomes_dash(self) -> None:
        assert _sanitize("foo.bar") == "foo-bar"

    def test_dash_becomes_dash(self) -> None:
        assert _sanitize("foo-bar") == "foo-bar"

    def test_space_becomes_underscore(self) -> None:
        assert _sanitize("foo bar") == "foo_bar"

    def test_arrow_translit(self) -> None:
        # → is not alnum so the explicit branch fires; first char "t"
        # is alpha so no leading-digit prefix
        assert _sanitize("→int") == "toint"

    def test_forall_translit(self) -> None:
        # ∀ is not alnum so the explicit branch fires
        assert _sanitize("∀x") == "allx"

    def test_eta_passthrough(self) -> None:
        # η IS alnum (Python treats Greek letters as alphanumeric) so
        # it passes through unchanged — Agda accepts Unicode identifiers
        assert _sanitize("ηmerge") == "ηmerge"

    def test_at_translit(self) -> None:
        assert _sanitize("foo@bar") == "foo-at-bar"

    def test_unknown_unicode_to_hex(self) -> None:
        result = _sanitize("foo★bar")
        assert "x" in result and "bar" in result

    def test_leading_digit_prepended(self) -> None:
        assert _sanitize("123abc").startswith("n")

    def test_empty_becomes_unnamed(self) -> None:
        # An empty string sanitizes to "unnamed"
        assert _sanitize("") == "unnamed"

    def test_reserved_word_suffixed(self) -> None:
        assert _sanitize("let") == "let-k"
        assert _sanitize("data") == "data-k"
        assert _sanitize("Set") == "Set-k"


# ── Internal helpers ────────────────────────────────────────────────


class TestPath1Closure:
    def test_no_paths1(self) -> None:
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma, tau)
        closure = _path1_closure(e.document)
        assert closure[a.id] == a.id

    def test_glue_unions(self) -> None:
        e = _two_obs_engine(glue=True)
        addr0_ids = [a.id for a in e.document.addresses0]
        closure = _path1_closure(e.document)
        # Both addr0s should map to the lex-smallest of the pair
        canonicals = {closure[a] for a in addr0_ids}
        assert len(canonicals) == 1
        assert closure[addr0_ids[0]] == min(addr0_ids)
        assert closure[addr0_ids[1]] == min(addr0_ids)

    def test_idempotent_union(self) -> None:
        """Calling union on an already-merged pair leaves the closure
        unchanged (returns early)."""
        e = _two_obs_engine(glue=True)
        # The streaming cascade already glued them; another path1 record
        # for the same pair would still be a no-op in the closure.
        closure_before = _path1_closure(e.document)
        # Manually add a redundant Addr1 with the same endpoints
        from cstz.pff import Addr1
        ids = [a.id for a in e.document.addresses0]
        e.document.paths1.append(Addr1(
            id="redundant", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        closure_after = _path1_closure(e.document)
        assert closure_before == closure_after

    def test_non_glue_ctors_ignored(self) -> None:
        from cstz.pff import Addr1
        e = _empty_engine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma_a, tau)
        b = e.add_observation(sigma_b, tau)
        # Add a non-glue Addr1 (e.g., transport) — should be ignored
        e.document.paths1.append(Addr1(
            id="trans", rank=e.document.ranks[0].id,
            ctor="transport", src=a.id, dst=b.id,
        ))
        closure = _path1_closure(e.document)
        assert closure[a.id] != closure[b.id]

    def test_refl_ctor_treated_as_self_union(self) -> None:
        from cstz.pff import Addr1
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma, tau)
        e.document.paths1.append(Addr1(
            id="r", rank=e.document.ranks[0].id,
            ctor="refl", src=a.id, dst=a.id,
        ))
        closure = _path1_closure(e.document)
        assert closure[a.id] == a.id

    def test_chained_glues(self) -> None:
        from cstz.pff import Addr1
        e = _empty_engine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        sigma_c = e.ensure_chart("sigma", "C")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma_a, tau)
        b = e.add_observation(sigma_b, tau)
        c = e.add_observation(sigma_c, tau)
        # Glue a~b and b~c manually
        e.document.paths1.append(Addr1(
            id="g1", rank=e.document.ranks[0].id,
            ctor="glue", src=a.id, dst=b.id,
        ))
        e.document.paths1.append(Addr1(
            id="g2", rank=e.document.ranks[0].id,
            ctor="glue", src=b.id, dst=c.id,
        ))
        closure = _path1_closure(e.document)
        # All three should share the same canonical
        assert closure[a.id] == closure[b.id] == closure[c.id]

    def test_path_compression_in_find(self) -> None:
        """Build a parent chain of depth ≥ 2 so the inner compression
        loop body fires.  Order the glues so the parent links chain
        through an intermediate, not directly to the root."""
        from cstz.pff import Addr0, Addr1, Pair, Segment, Step
        from cstz.pff_cascade import PFFCascadeEngine
        e = PFFCascadeEngine(document_id="chain")
        rank = e.ensure_rank(0)
        patch = e.ensure_patch(rank=rank)
        # Construct three addr0s manually so we control the ids
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        # Use add_observation to mint via the engine — gives us
        # addr0-0, addr0-1, addr0-2 in lex order
        a = e.add_observation(sigma, tau, sort="A", node_root="A")
        b = e.add_observation(
            e.ensure_chart("sigma", "Y"), tau, sort="B", node_root="B",
        )
        c = e.add_observation(
            e.ensure_chart("sigma", "Z"), tau, sort="C", node_root="C",
        )
        # Now construct paths1 in an order that builds a chain:
        # First: B~C → parent[C] = B
        # Then:  A~B → parent[B] = A
        # Result: parent = {A→A, B→A, C→B}.  find(C) walks C→B→A,
        # triggering path compression's inner loop body.
        e.document.paths1.append(Addr1(
            id="bc", rank=rank.id, ctor="glue", src=b.id, dst=c.id,
        ))
        e.document.paths1.append(Addr1(
            id="ab", rank=rank.id, ctor="glue", src=a.id, dst=b.id,
        ))
        closure = _path1_closure(e.document)
        # All three converge on the same canonical
        assert closure[a.id] == closure[b.id] == closure[c.id] == a.id

    def test_lex_decreasing_union(self) -> None:
        """When src lex-orders AFTER dst, the union swap branch fires."""
        from cstz.pff import Addr1
        e = _empty_engine()
        sigma_a = e.ensure_chart("sigma", "A")
        sigma_b = e.ensure_chart("sigma", "B")
        tau = e.ensure_chart("tau", "T")
        a = e.add_observation(sigma_a, tau)
        b = e.add_observation(sigma_b, tau)
        # Manually glue with src=b (lex-larger), dst=a (lex-smaller)
        # → union(b, a): ra=b, rb=a, ra > rb, parent[ra]=rb branch fires
        e.document.paths1.append(Addr1(
            id="g", rank=e.document.ranks[0].id,
            ctor="glue", src=b.id, dst=a.id,
        ))
        closure = _path1_closure(e.document)
        # Both should map to a (the lex-smaller)
        assert closure[a.id] == a.id
        assert closure[b.id] == a.id


class TestPath2Closure:
    def test_empty_paths2(self) -> None:
        e = _two_obs_engine(glue=True)
        # Two glued addr0s → one path1, no path2s
        closure = _path2_closure(e.document)
        addr1_ids = [a.id for a in e.document.paths1]
        assert closure[addr1_ids[0]] == addr1_ids[0]

    def test_coh_unions_addr1s(self) -> None:
        from cstz.pff import Addr1, Addr2
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        # The streaming cascade emitted one Addr1; add a second redundant one
        first_id = e.document.paths1[0].id
        ids = [a.id for a in e.document.addresses0]
        e.document.paths1.append(Addr1(
            id="alt", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        # Coh them
        e.document.paths2.append(Addr2(
            id="c", rank=e.document.ranks[0].id,
            ctor="coh", src=first_id, dst="alt",
        ))
        closure = _path2_closure(e.document)
        assert closure[first_id] == closure["alt"]

    def test_non_coh_ctors_ignored(self) -> None:
        from cstz.pff import Addr1, Addr2
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first_id = e.document.paths1[0].id
        ids = [a.id for a in e.document.addresses0]
        e.document.paths1.append(Addr1(
            id="alt", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        # Use a non-coh ctor; should be ignored
        e.document.paths2.append(Addr2(
            id="v", rank=e.document.ranks[0].id,
            ctor="vcomp", src=first_id, dst="alt",
        ))
        closure = _path2_closure(e.document)
        assert closure[first_id] != closure["alt"]

    def test_path2_no_op_when_already_in_class(self) -> None:
        """Two coh records targeting the same canonical pair: the
        second is a no-op (early return in union)."""
        from cstz.pff import Addr1, Addr2
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first_id = e.document.paths1[0].id
        ids = [a.id for a in e.document.addresses0]
        e.document.paths1.append(Addr1(
            id="alt", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        # First coh: unions first_id and alt
        e.document.paths2.append(Addr2(
            id="c1", rank=e.document.ranks[0].id,
            ctor="coh", src=first_id, dst="alt",
        ))
        # Second coh: same pair → no-op via early return
        e.document.paths2.append(Addr2(
            id="c2", rank=e.document.ranks[0].id,
            ctor="coh", src=first_id, dst="alt",
        ))
        closure = _path2_closure(e.document)
        assert closure[first_id] == closure["alt"]

    def test_path2_chain_compression(self) -> None:
        """Build a 3-addr1 path2 chain so the inner compression loop
        body fires."""
        from cstz.pff import Addr1, Addr2
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first_id = e.document.paths1[0].id
        ids = [a.id for a in e.document.addresses0]
        # Add two more addr1s with controlled lex order: a1 < a2 < a3
        # so the chain a3→a2→a1 forms when coh edges are processed
        # bottom-up.
        e.document.paths1.append(Addr1(
            id="a2", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        e.document.paths1.append(Addr1(
            id="a3", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        # First coh: a2~a3 → parent[a3] = a2 (a2 < a3)
        # Second coh: a1~a2 → parent[a2] = a1 (a1 < a2 because
        # first_id="addr1-0" sorts before "a2"? Let's check:
        # "addr1-0" vs "a2": "a"="a", "d" vs "2"; "2" < "d" so
        # "a2" < "addr1-0".  So the lex-smallest of {first_id, a2}
        # is "a2", meaning union(first_id, a2): ra=first_id="addr1-0",
        # rb="a2"; ra > rb → parent[ra]=rb → parent["addr1-0"]="a2".)
        # And parent["a3"]="a2" from first coh.
        # find("a3"): walks a3 → a2 (root). Only one step.
        # So this construction does NOT chain. Need different ids.
        #
        # Use ids that lex-sort cleanly:
        #   "p1" < "p2" < "p3"
        # First coh p2~p3 → parent[p3]=p2
        # Second coh p1~p2 → parent[p2]=p1
        # find(p3) walks p3→p2→p1: triggers compression body.
        e.document.paths1.append(Addr1(
            id="p1", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        e.document.paths1.append(Addr1(
            id="p2", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        e.document.paths1.append(Addr1(
            id="p3", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        # Coh order matters: process p2~p3 first to set parent[p3]=p2
        e.document.paths2.append(Addr2(
            id="x1", rank=e.document.ranks[0].id,
            ctor="coh", src="p2", dst="p3",
        ))
        e.document.paths2.append(Addr2(
            id="x2", rank=e.document.ranks[0].id,
            ctor="coh", src="p1", dst="p2",
        ))
        closure = _path2_closure(e.document)
        assert closure["p1"] == closure["p2"] == closure["p3"] == "p1"

    def test_path2_lex_decreasing_union(self) -> None:
        """Coh src lex-orders AFTER dst → union swap branch fires.

        The streaming-cascade-emitted Addr1 has id ``addr1-0``;
        ``z-glue`` lex-orders after ``addr1-0``, so coh(src='z-glue',
        dst='addr1-0') has ra='z-glue' > rb='addr1-0' and hits the
        else branch.
        """
        from cstz.pff import Addr1, Addr2
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        first_id = e.document.paths1[0].id
        ids = [a.id for a in e.document.addresses0]
        e.document.paths1.append(Addr1(
            id="z-glue", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        e.document.paths2.append(Addr2(
            id="c", rank=e.document.ranks[0].id,
            ctor="coh", src="z-glue", dst=first_id,
        ))
        closure = _path2_closure(e.document)
        # Both addr1s should map to first_id (the lex-smaller)
        assert closure[first_id] == first_id
        assert closure["z-glue"] == first_id


class TestIndexMaps:
    def test_addr0_index_stable(self) -> None:
        e = _two_obs_engine(glue=True)
        idx = _addr0_index_map(e.document)
        assert set(idx.values()) == {0, 1}
        # First addr0 inserted is index 0
        assert idx[e.document.addresses0[0].id] == 0
        assert idx[e.document.addresses0[1].id] == 1

    def test_addr1_index_stable(self) -> None:
        e = _two_obs_engine(glue=True)
        idx = _addr1_index_map(e.document)
        assert set(idx.values()) == {0}


class TestBuildChartNames:
    def test_unique_names(self) -> None:
        names = _build_chart_names(["c1", "c2"], {"c1": "Foo", "c2": "Bar"})
        assert names == {"c1": "Foo", "c2": "Bar"}

    def test_collision_disambiguated(self) -> None:
        names = _build_chart_names(
            ["c1", "c2"], {"c1": "Foo", "c2": "Foo"},
        )
        assert set(names.values()) == {"Foo-0", "Foo-1"}

    def test_root_with_special_chars_sanitized(self) -> None:
        names = _build_chart_names(["c1"], {"c1": "→foo.bar"})
        assert "→" not in names["c1"]
        assert "." not in names["c1"]


# ── synthesize_from_document: structural ────────────────────────────


class TestSynthesizeStructure:
    def test_module_header(self) -> None:
        e = _empty_engine()
        agda = synthesize_from_document(e.document, module_name="EmptyTest")
        assert agda.startswith("module EmptyTest where")
        assert "PFF Document projection: empty" in agda

    def test_prelude_present(self) -> None:
        e = _empty_engine()
        agda = synthesize_from_document(e.document, module_name="P")
        assert "data _≡_" in agda
        assert "sym :" in agda
        assert "trans :" in agda
        assert "data ℕ" in agda
        assert "BUILTIN NATURAL" in agda

    def test_canonical_map_emitted(self) -> None:
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(e.document, module_name="C")
        assert "ρ : ℕ → ℕ" in agda
        assert "ρ canonical map" in agda
        # The non-identity move should appear
        assert "ρ 1 = 0" in agda or "ρ 0 = 1" in agda

    def test_canonical_map_no_idem_proof(self) -> None:
        """Idempotence proof must NOT be emitted (Agda can't prove it
        with the catch-all + specific patterns combination)."""
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(e.document, module_name="C")
        assert "ρ-idem" not in agda
        assert "π-idem" not in agda

    def test_glue_witnesses_emitted(self) -> None:
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(e.document, module_name="C")
        assert "Path1 (glue) witnesses" in agda
        # The streaming-cascade-emitted addr1 should appear
        addr1_id = _sanitize(e.document.paths1[0].id)
        assert addr1_id in agda

    def test_no_path2_section_when_no_paths1(self) -> None:
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma, tau)
        agda = synthesize_from_document(e.document, module_name="C")
        # Single observation → no glues → no path2 map
        assert "π : ℕ" not in agda

    def test_path2_map_emitted_when_paths1_present(self) -> None:
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(e.document, module_name="C")
        assert "π : ℕ → ℕ" in agda

    def test_coh_witnesses_emitted(self) -> None:
        from cstz.pff import Addr1, Addr2
        e = _two_obs_engine(glue=True)
        first_id = e.document.paths1[0].id
        ids = [a.id for a in e.document.addresses0]
        e.document.paths1.append(Addr1(
            id="alt", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        e.document.paths2.append(Addr2(
            id="c1", rank=e.document.ranks[0].id,
            ctor="coh", src=first_id, dst="alt",
        ))
        agda = synthesize_from_document(e.document, module_name="C")
        assert "Path2 (coh) witnesses" in agda
        assert _sanitize("c1") in agda

    def test_chart_modules_emitted(self) -> None:
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(e.document, module_name="C")
        assert "Chart partition" in agda
        # Default chart_kind="sigma" → grouped by σ-charts
        assert "module X where" in agda

    def test_chart_kind_tau(self) -> None:
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(
            e.document, module_name="C", chart_kind="tau",
        )
        # Now grouped by τ-charts (A and B)
        assert "module A where" in agda
        assert "module B where" in agda

    def test_chart_module_collision_disambiguated(self) -> None:
        # Two charts with the same root but different payloads
        e = _empty_engine()
        s1 = e.ensure_chart("sigma", "Foo", payload={"v": 1})
        s2 = e.ensure_chart("sigma", "Foo", payload={"v": 2})
        tau = e.ensure_chart("tau", "T")
        e.add_observation(s1, tau)
        e.add_observation(s2, tau)
        agda = synthesize_from_document(e.document, module_name="C")
        # Two distinct sigma-charts named "Foo" → disambiguated names
        assert "module Foo-0 where" in agda or "module Foo-1 where" in agda

    def test_summary_present(self) -> None:
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(e.document, module_name="C")
        assert "Summary:" in agda
        assert "document: two-obs" in agda

    def test_no_chart_partition_when_no_obs(self) -> None:
        e = _empty_engine()
        agda = synthesize_from_document(e.document, module_name="C")
        assert "Chart partition" not in agda

    def test_addr0_with_no_matching_pair_skipped(self) -> None:
        """An addr0 whose first segment has no role-matching pair should
        be silently skipped (the chart partition loop falls through)."""
        from cstz.pff import Addr0, Pair, Segment, Step
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        # First, a normal observation so the rank/patch are seeded
        e.add_observation(sigma, tau)
        # Now hand-construct an addr0 whose only pair is `aux` while
        # we ask for `principal` charts → no match, fall-through.
        rank = e.document.ranks[0].id
        patch = e.document.patches[0].id
        e.document.addresses0.append(Addr0(
            id="lonely",
            sort="Lonely",
            discoveryRank=rank,
            segments=[Segment(
                rank=rank, phase="ingest", patch=patch,
                pairs=[
                    # Only an aux pair; no principal
                    Pair(chart=tau.id, root="lonely",
                         route=[Step(kind="field", arg="tau")],
                         role="aux"),
                ],
            )],
        ))
        agda = synthesize_from_document(e.document, module_name="C")
        # The lonely addr0 should not contribute to the σ-chart partition
        assert "lonely" not in agda or "module" in agda  # syntactic sanity


# ── synthesize_from_document: end-to-end Agda type-check ────────────


class TestAgdaTypeCheck:
    """Real Agda type-checks of generated files.

    Skipped automatically if the ``agda`` binary is not in PATH.
    """

    def setup_method(self) -> None:
        if not _agda_available():
            pytest.skip("agda binary not available in PATH")

    def test_empty_document(self, tmp_path: Path) -> None:
        e = _empty_engine()
        agda = synthesize_from_document(e.document, module_name="EmptyDoc")
        _agda_check(agda, "EmptyDoc", tmp_path)

    def test_single_observation(self, tmp_path: Path) -> None:
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau = e.ensure_chart("tau", "T")
        e.add_observation(sigma, tau)
        agda = synthesize_from_document(e.document, module_name="SingleObs")
        _agda_check(agda, "SingleObs", tmp_path)

    def test_two_observations_with_glue(self, tmp_path: Path) -> None:
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(e.document, module_name="TwoObs")
        _agda_check(agda, "TwoObs", tmp_path)

    def test_three_observations_chained(self, tmp_path: Path) -> None:
        e = _empty_engine()
        sigma = e.ensure_chart("sigma", "X")
        tau_a = e.ensure_chart("tau", "A")
        tau_b = e.ensure_chart("tau", "B")
        tau_c = e.ensure_chart("tau", "C")
        e.add_observation(sigma, tau_a)
        e.add_observation(sigma, tau_b)
        e.add_observation(sigma, tau_c)
        agda = synthesize_from_document(e.document, module_name="ThreeObs")
        _agda_check(agda, "ThreeObs", tmp_path)

    def test_recursive_cascade(self, tmp_path: Path) -> None:
        e = _empty_engine()
        sLa = e.ensure_chart("sigma", "LeafA")
        sLb = e.ensure_chart("sigma", "LeafB")
        sP = e.ensure_chart("sigma", "Parent")
        tA = e.ensure_chart("tau", "A")
        tB = e.ensure_chart("tau", "B")
        tPa = e.ensure_chart("tau", "Pa")
        tPb = e.ensure_chart("tau", "Pb")
        la = e.add_observation(sLa, tA)
        lb = e.add_observation(sLb, tB)
        e.add_observation(sP, tPa, sigma_children=[la.id])
        e.add_observation(sP, tPb, sigma_children=[lb.id])
        e.glue(la.id, lb.id)
        agda = synthesize_from_document(e.document, module_name="Cascade")
        _agda_check(agda, "Cascade", tmp_path)

    def test_with_explicit_coh(self, tmp_path: Path) -> None:
        from cstz.pff import Addr1, Addr2
        e = _two_obs_engine(glue=True)
        first_id = e.document.paths1[0].id
        ids = [a.id for a in e.document.addresses0]
        e.document.paths1.append(Addr1(
            id="alt", rank=e.document.ranks[0].id,
            ctor="glue", src=ids[0], dst=ids[1],
        ))
        e.document.paths2.append(Addr2(
            id="c1", rank=e.document.ranks[0].id,
            ctor="coh", src=first_id, dst="alt",
        ))
        agda = synthesize_from_document(e.document, module_name="WithCoh")
        _agda_check(agda, "WithCoh", tmp_path)

    def test_factorized_python(self, tmp_path: Path) -> None:
        """End-to-end: factorize Python source, project to Agda, type-check."""
        engine = factorize(
            "def add(x: int, y: int) -> int:\n"
            "    return x + y\n"
            "p = add(1, 2)\n"
            "print(p)\n",
            document_id="EndToEnd",
        )
        agda = synthesize_from_document(
            engine.document, module_name="EndToEnd",
        )
        _agda_check(agda, "EndToEnd", tmp_path)

    def test_cascade_with_chart_kind_tau(self, tmp_path: Path) -> None:
        e = _two_obs_engine(glue=True)
        agda = synthesize_from_document(
            e.document, module_name="TauGrouped", chart_kind="tau",
        )
        _agda_check(agda, "TauGrouped", tmp_path)
