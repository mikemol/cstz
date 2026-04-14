"""Tests for cstz.observe — the observation protocol.

Every test validates CSTZ-native semantics: operationalist equivalence,
profile accumulation via OR, regime monotonicity, S₃ symmetry.
"""

import pytest
from cstz.gf2 import dot, basis
from cstz.framework import GAP, ORDERED_TAU, ORDERED_SIGMA, OVER, CellKind
from cstz.observe import Observation, Patch, ObservationState

# GF(2)^3 elements and discriminators
e1, e2, e3 = 0b100, 0b010, 0b001
a0, a1, a2, a3, a4, a5, a6, a7 = range(8)


class TestObservation:
    def test_frozen(self):
        obs = Observation(element=a5, discriminator=e1, result=ORDERED_TAU)
        assert obs.element == a5
        assert obs.discriminator == e1
        assert obs.result == ORDERED_TAU

    def test_equality(self):
        o1 = Observation(a5, e1, ORDERED_TAU)
        o2 = Observation(a5, e1, ORDERED_TAU)
        assert o1 == o2


class TestPatch:
    def test_observe(self):
        p = Patch()
        obs = p.observe(a5, e1, ORDERED_TAU)
        assert obs in p.observations
        assert e1 in p.regime

    def test_observe_with_eval(self):
        """dot(e1, a5) = 1 → τ fires; dot(e2, a5) = 0 → σ silent.
        Profile = (1,0) = ORDERED_TAU."""
        p = Patch()
        obs = p.observe_with_eval(dot, e1, e2, a5)
        assert obs.result == ORDERED_TAU

    def test_regime_grows(self):
        p = Patch()
        p.observe(a0, e1, GAP)
        p.observe(a0, e2, GAP)
        assert p.regime == [e1, e2]
        assert p.dim == 2

    def test_regime_no_duplicates(self):
        p = Patch()
        p.observe(a0, e1, GAP)
        p.observe(a1, e1, GAP)
        assert p.regime == [e1]

    def test_elements(self):
        p = Patch()
        p.observe(a0, e1, GAP)
        p.observe(a5, e1, ORDERED_TAU)
        assert p.elements() == {a0, a5}

    def test_discriminators(self):
        p = Patch()
        p.observe(a0, e1, GAP)
        p.observe(a0, e2, ORDERED_TAU)
        assert p.discriminators() == {e1, e2}


class TestObservationState:
    def _make_simple_state(self):
        """Create a state with a₀-a₇ observed under e₁."""
        state = ObservationState(dim=3)
        p = state.new_patch()
        for elem in range(8):
            tau_val = dot(e1, elem)
            p.observe(elem, e1, (tau_val << 1))  # tau only, sigma=0
        return state

    def test_new_patch(self):
        state = ObservationState(dim=3)
        p = state.new_patch()
        assert p in state.patches

    def test_merge(self):
        state = ObservationState(dim=3)
        p = Patch()
        p.observe(a5, e1, ORDERED_TAU)
        state.merge(p)
        assert len(state.patches) == 1
        assert state.all_elements() == {a5}

    def test_regime_union(self):
        state = ObservationState(dim=3)
        p1 = state.new_patch()
        p1.observe(a0, e1, GAP)
        p2 = state.new_patch()
        p2.observe(a0, e2, GAP)
        assert set(state.regime) == {e1, e2}

    def test_regime_dedup(self):
        """Shared discriminators appear only once in combined regime."""
        state = ObservationState(dim=3)
        p1 = state.new_patch()
        p1.observe(a0, e1, GAP)
        p2 = state.new_patch()
        p2.observe(a1, e1, GAP)  # same discriminator
        assert state.regime == [e1]  # not [e1, e1]

    def test_profile_accumulation_or(self):
        """Two patches observing the same element: results OR together."""
        state = ObservationState(dim=3)
        p1 = state.new_patch()
        p1.observe(a5, e1, ORDERED_TAU)   # (1,0)
        p2 = state.new_patch()
        p2.observe(a5, e1, ORDERED_SIGMA)  # (0,1)
        # Accumulated: (1,0) | (0,1) = (1,1) = OVER
        assert state.profile(a5) == OVER

    def test_profile_gap_identity(self):
        """GAP is identity under OR: gap | x = x."""
        state = ObservationState(dim=3)
        p = state.new_patch()
        p.observe(a5, e1, GAP)
        assert state.profile(a5) == GAP
        p.observe(a5, e1, ORDERED_TAU)
        assert state.profile(a5) == ORDERED_TAU

    def test_profile_unobserved(self):
        """Unobserved elements have GAP profile."""
        state = ObservationState(dim=3)
        state.new_patch()
        assert state.profile(a0) == GAP

    def test_equiv_same_element(self):
        state = self._make_simple_state()
        assert state.equiv(a0, a0)

    def test_equiv_indistinguishable(self):
        """a₀ and a₁ are indistinguishable under e₁ alone."""
        state = self._make_simple_state()
        # e1(a0)=0, e1(a1)=0 → same profile under e1
        assert state.equiv(a0, a1)

    def test_equiv_distinguishable(self):
        """a₀ and a₄ are distinguishable under e₁."""
        state = self._make_simple_state()
        # e1(a0)=0, e1(a4)=1 → different profiles
        assert not state.equiv(a0, a4)

    def test_classify_element(self):
        state = ObservationState(dim=3)
        p = state.new_patch()
        p.observe(a5, e1, ORDERED_TAU)
        assert state.classify_element(a5) == CellKind.ORDERED_TAU

    def test_regime_dim(self):
        state = ObservationState(dim=3)
        p1 = state.new_patch()
        p1.observe(a0, e1, GAP)
        p2 = state.new_patch()
        p2.observe(a0, e2, GAP)
        assert state.regime_dim == 2

    def test_residue_elements(self):
        state = ObservationState(dim=3)
        p = state.new_patch()
        p.observe(a0, e1, GAP)
        p.observe(a5, e1, ORDERED_TAU)
        assert a0 in state.residue_elements()
        assert a5 not in state.residue_elements()

    def test_boolean_elements(self):
        state = ObservationState(dim=3)
        p = state.new_patch()
        p.observe(a0, e1, GAP)
        p.observe(a5, e1, ORDERED_TAU)
        p.observe(a2, e1, ORDERED_SIGMA)
        assert a5 in state.boolean_elements()
        assert a2 in state.boolean_elements()
        assert a0 not in state.boolean_elements()

    def test_equivalence_classes(self):
        """Under e₁ alone: {a₀,a₁,a₂,a₃} and {a₄,a₅,a₆,a₇}."""
        state = self._make_simple_state()
        classes = state.equivalence_classes()
        # Should have 2 classes
        assert len(classes) == 2
        sizes = sorted(len(v) for v in classes.values())
        assert sizes == [4, 4]

    def test_equivalence_classes_full_regime(self):
        """Under e₁,e₂,e₃: all 8 elements distinct (singletons)."""
        state = ObservationState(dim=3)
        p = state.new_patch()
        for elem in range(8):
            for d in [e1, e2, e3]:
                tau_val = dot(d, elem)
                p.observe(elem, d, (tau_val << 1))
        classes = state.equivalence_classes()
        assert len(classes) == 8
        for members in classes.values():
            assert len(members) == 1

    def test_multi_patch_merge(self):
        """Two patches with orthogonal discriminators merge cleanly."""
        state = ObservationState(dim=3)

        p1 = state.new_patch()
        for elem in range(8):
            p1.observe(elem, e1, (dot(e1, elem) << 1))

        p2 = state.new_patch()
        for elem in range(8):
            p2.observe(elem, e2, (dot(e2, elem) << 1))

        # Combined regime has both discriminators
        assert set(state.regime) == {e1, e2}

        # a₀ and a₁ equivalent under e₁ alone but now e₂ might separate
        # e2(a0)=0, e2(a1)=0 → still equivalent
        assert state.equiv(a0, a1)
        # e2(a0)=0, e2(a2)=1 → now separated
        assert not state.equiv(a0, a2)

    def test_all_elements(self):
        state = ObservationState(dim=3)
        p = state.new_patch()
        p.observe(a0, e1, GAP)
        p.observe(a7, e1, ORDERED_TAU)
        assert state.all_elements() == {a0, a7}
