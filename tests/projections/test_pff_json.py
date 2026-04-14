"""Tests for cstz.projections.pff_json — PFF JSON projection."""

import json
import pytest
from cstz.gf2 import dot
from cstz.framework import GAP, ORDERED_TAU, ORDERED_SIGMA, OVER
from cstz.observe import Observation, ObservationState, Patch
from cstz.projections.pff_json import observation_state_to_pff, VERSION, IDENTIFIER_SCOPE

e1, e2, e3 = 0b100, 0b010, 0b001


def _make_gf2_cubed_state():
    """Create a state with all 8 elements observed under e₁."""
    state = ObservationState(dim=3)
    p = state.new_patch()
    for elem in range(8):
        tau_val = dot(e1, elem)
        p.observe(elem, e1, (tau_val << 1))
    return state


class TestPffJsonProjection:
    def test_version(self):
        state = ObservationState(dim=3)
        state.new_patch()
        doc = observation_state_to_pff(state)
        assert doc["version"] == VERSION

    def test_identifier_scope(self):
        state = ObservationState(dim=3)
        state.new_patch()
        doc = observation_state_to_pff(state)
        assert doc["identifierScope"] == IDENTIFIER_SCOPE

    def test_document_id(self):
        state = ObservationState(dim=3)
        state.new_patch()
        doc = observation_state_to_pff(state, document_id="test-doc")
        assert doc["documentId"] == "test-doc"

    def test_required_fields_present(self):
        state = ObservationState(dim=3)
        state.new_patch()
        doc = observation_state_to_pff(state)
        for field in ["version", "documentId", "identifierScope",
                       "ranks", "patches", "charts", "addresses0"]:
            assert field in doc, f"Missing required field: {field}"

    def test_ranks_from_regime(self):
        state = _make_gf2_cubed_state()
        doc = observation_state_to_pff(state)
        assert len(doc["ranks"]) == 1  # one discriminator = one rank
        assert doc["ranks"][0]["ordinal"] == 0

    def test_patches_from_patches(self):
        state = _make_gf2_cubed_state()
        doc = observation_state_to_pff(state)
        assert len(doc["patches"]) == 1

    def test_addresses0_from_elements(self):
        state = _make_gf2_cubed_state()
        doc = observation_state_to_pff(state)
        assert len(doc["addresses0"]) == 8  # 8 elements observed

    def test_addr0_has_segments(self):
        state = _make_gf2_cubed_state()
        doc = observation_state_to_pff(state)
        for addr0 in doc["addresses0"]:
            assert "segments" in addr0
            assert len(addr0["segments"]) >= 1
            for seg in addr0["segments"]:
                assert "pairs" in seg
                assert len(seg["pairs"]) >= 1

    def test_pair_has_role(self):
        state = _make_gf2_cubed_state()
        doc = observation_state_to_pff(state)
        for addr0 in doc["addresses0"]:
            for seg in addr0["segments"]:
                for pair in seg["pairs"]:
                    assert pair["role"] in ("principal", "aux")

    def test_charts_sigma_and_tau(self):
        state = _make_gf2_cubed_state()
        doc = observation_state_to_pff(state)
        # One discriminator → one sigma chart + one tau chart
        assert len(doc["charts"]) == 2
        kinds = {c.get("kind") for c in doc["charts"]}
        assert kinds == {"sigma", "tau"}

    def test_serializable_as_json(self):
        """The output should be valid JSON (all types serializable)."""
        state = _make_gf2_cubed_state()
        doc = observation_state_to_pff(state)
        json_str = json.dumps(doc)
        parsed = json.loads(json_str)
        assert parsed["version"] == VERSION

    def test_empty_state(self):
        """Empty state should still produce valid structure."""
        state = ObservationState(dim=3)
        state.new_patch()
        doc = observation_state_to_pff(state)
        assert len(doc["ranks"]) >= 1  # schema requires minItems: 1
        assert len(doc["addresses0"]) == 0

    def test_multi_discriminator(self):
        """Two discriminators → two ranks, four charts."""
        state = ObservationState(dim=3)
        p = state.new_patch()
        for elem in range(8):
            p.observe(elem, e1, (dot(e1, elem) << 1))
            p.observe(elem, e2, (dot(e2, elem) << 1))
        doc = observation_state_to_pff(state)
        assert len(doc["ranks"]) == 2
        assert len(doc["charts"]) == 4  # 2 disc × (sigma + tau)

    def test_multi_patch(self):
        """Two patches → two patch records."""
        state = ObservationState(dim=3)
        p1 = state.new_patch()
        p1.observe(0, e1, GAP)
        p2 = state.new_patch()
        p2.observe(1, e2, ORDERED_TAU)
        doc = observation_state_to_pff(state)
        assert len(doc["patches"]) == 2

    def test_ids_are_strings(self):
        state = _make_gf2_cubed_state()
        doc = observation_state_to_pff(state)
        for addr0 in doc["addresses0"]:
            assert isinstance(addr0["id"], str)
        for rank in doc["ranks"]:
            assert isinstance(rank["id"], str)

    def test_empty_regime_patch(self):
        """A patch with manually added observations but empty regime."""
        state = ObservationState(dim=3)
        p = Patch()
        # Manually add observation without going through observe()
        p.observations.append(Observation(element=0, discriminator=e1, result=GAP))
        state.merge(p)
        doc = observation_state_to_pff(state)
        # Should still produce valid output
        assert len(doc["addresses0"]) == 1
