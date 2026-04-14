"""Tests for cstz.classify.adapter — the Classified → Observation projection."""

import pytest
from cstz.classify.adapter import emit_patch
from cstz.classify.base import Classified, ShapeWitness
from cstz.framework import ORDERED_TAU
from cstz.observe import Patch


def _leaf_shape():
    return ShapeWitness(0, ())


class TestEmitPatch:
    def test_silence(self):
        """τ=0 emits zero observations, touches no regime."""
        patch = Patch()
        items = [(0b1, Classified(tau=0, shape=_leaf_shape()))]
        emit_patch(items, patch)
        assert patch.observations == []
        assert patch.regime == []

    def test_single_bit(self):
        """τ with one bit emits exactly one observation."""
        patch = Patch()
        items = [(0b1, Classified(tau=0b100, shape=_leaf_shape()))]
        emit_patch(items, patch)
        assert len(patch.observations) == 1
        obs = patch.observations[0]
        assert obs.element == 0b1
        assert obs.discriminator == 0b100
        assert obs.result == ORDERED_TAU

    def test_multiple_bits(self):
        """τ with k bits emits exactly k observations (one per bit)."""
        patch = Patch()
        tau = 0b1011  # three bits: 1, 2, 8
        items = [(0b1, Classified(tau=tau, shape=_leaf_shape()))]
        emit_patch(items, patch)
        assert len(patch.observations) == 3
        disc_ids = {o.discriminator for o in patch.observations}
        assert disc_ids == {0b0001, 0b0010, 0b1000}

    def test_all_are_ordered_tau(self):
        """Every emitted observation has result=ORDERED_TAU (never σ)."""
        patch = Patch()
        items = [(0b1, Classified(tau=0b1111, shape=_leaf_shape()))]
        emit_patch(items, patch)
        for obs in patch.observations:
            assert obs.result == ORDERED_TAU

    def test_multiple_nodes(self):
        """Observations from multiple nodes accumulate."""
        patch = Patch()
        items = [
            (0b1, Classified(tau=0b01, shape=_leaf_shape())),
            (0b10, Classified(tau=0b10, shape=_leaf_shape())),
            (0b11, Classified(tau=0b11, shape=_leaf_shape())),
        ]
        emit_patch(items, patch)
        # 1 + 1 + 2 = 4 observations
        assert len(patch.observations) == 4

    def test_zpath_becomes_element(self):
        """The zpath int is used as the Observation element bitvector."""
        patch = Patch()
        items = [
            (0b1, Classified(tau=0b1, shape=_leaf_shape())),
            (0b101, Classified(tau=0b1, shape=_leaf_shape())),
            (0b1111, Classified(tau=0b1, shape=_leaf_shape())),
        ]
        emit_patch(items, patch)
        elements = {o.element for o in patch.observations}
        assert elements == {0b1, 0b101, 0b1111}

    def test_regime_tracks_discriminators(self):
        """Observed discriminators enter the patch regime."""
        patch = Patch()
        items = [(0b1, Classified(tau=0b101, shape=_leaf_shape()))]
        emit_patch(items, patch)
        assert set(patch.regime) == {0b001, 0b100}

    def test_empty_items(self):
        """Empty iterable yields empty patch."""
        patch = Patch()
        emit_patch([], patch)
        assert patch.observations == []
        assert patch.regime == []

    def test_popcount_matches_observation_count(self):
        """Exhaustive: for each τ in 0..2^k, observation count == popcount(τ)."""
        for tau in range(16):
            patch = Patch()
            items = [(0b1, Classified(tau=tau, shape=_leaf_shape()))]
            emit_patch(items, patch)
            expected = bin(tau).count("1")
            assert len(patch.observations) == expected, \
                f"τ={tau:#06b} expected {expected}, got {len(patch.observations)}"

    def test_monotone(self):
        """τ'⊇τ produces a superset of observations (at same zpath)."""
        # τ = 0b001
        p1 = Patch()
        emit_patch([(0b1, Classified(0b001, _leaf_shape()))], p1)
        # τ' = 0b011 ⊇ 0b001
        p2 = Patch()
        emit_patch([(0b1, Classified(0b011, _leaf_shape()))], p2)
        # p2's observations are a superset of p1's (matched by (element, disc))
        set1 = {(o.element, o.discriminator) for o in p1.observations}
        set2 = {(o.element, o.discriminator) for o in p2.observations}
        assert set1 < set2

    def test_injective(self):
        """Distinct τ-bits produce distinct Observations (no collisions)."""
        patch = Patch()
        # Two different bits, same zpath: two distinct observations
        items = [(0b1, Classified(tau=0b11, shape=_leaf_shape()))]
        emit_patch(items, patch)
        # Distinct discriminator IDs → distinct observations
        pairs = [(o.element, o.discriminator) for o in patch.observations]
        assert len(set(pairs)) == len(pairs)
