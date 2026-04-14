"""Tests for cstz.disc.framework and cstz.disc.axioms."""

import pytest
from cstz.disc.gf2 import dot, basis
from cstz.disc.framework import (
    GAP, ORDERED_SIGMA, ORDERED_TAU, OVER, CellKind,
    classify, chi, is_residue, is_boolean,
    profile, evolve, dim_kappa, membership,
)
from cstz.disc.axioms import (
    check_profile_linearity, check_eval_linearity,
    check_bilinearity, check_operationalist,
)

# Concrete eval: dot product over GF(2)
eval_dot = dot

# GF(2)^3 elements
e1, e2, e3 = 0b100, 0b010, 0b001
a0, a1, a2, a5, a6 = 0b000, 0b001, 0b010, 0b101, 0b110


class TestFourCell:
    def test_classify_all(self):
        assert classify(GAP) == CellKind.GAP
        assert classify(ORDERED_SIGMA) == CellKind.ORDERED_SIGMA
        assert classify(ORDERED_TAU) == CellKind.ORDERED_TAU
        assert classify(OVER) == CellKind.OVER

    def test_chi(self):
        assert chi(GAP) == 0           # residue
        assert chi(ORDERED_TAU) == 1   # boolean
        assert chi(ORDERED_SIGMA) == 1 # boolean
        assert chi(OVER) == 0          # residue

    def test_residue(self):
        assert is_residue(GAP)
        assert is_residue(OVER)
        assert not is_residue(ORDERED_TAU)
        assert not is_residue(ORDERED_SIGMA)

    def test_boolean(self):
        assert is_boolean(ORDERED_TAU)
        assert is_boolean(ORDERED_SIGMA)
        assert not is_boolean(GAP)
        assert not is_boolean(OVER)


class TestProfile:
    def test_profile_a5(self):
        """Agda: profile of a₅ under (e₁, e₂) = (1,0) = ORDERED_TAU."""
        p = profile(eval_dot, e1, e2, a5)
        assert p == ORDERED_TAU  # τ=1, σ=0

    def test_profile_a2(self):
        """a₂=010 under (e₁,e₂): τ=e₁(010)=0, σ=e₂(010)=1 → ORDERED_SIGMA."""
        p = profile(eval_dot, e1, e2, a2)
        assert p == ORDERED_SIGMA

    def test_profile_a0(self):
        """a₀=000 under (e₁,e₂): τ=0, σ=0 → GAP."""
        p = profile(eval_dot, e1, e2, a0)
        assert p == GAP

    def test_profile_a6(self):
        """a₆=110 under (e₁,e₂): τ=1, σ=1 → OVER."""
        p = profile(eval_dot, e1, e2, a6)
        assert p == OVER


class TestRegime:
    def test_evolve(self):
        r0 = []
        r1 = evolve(r0, e1)
        r2 = evolve(r1, e2)
        assert r1 == [e1]
        assert r2 == [e1, e2]

    def test_dim_kappa(self):
        assert dim_kappa([]) == 0
        assert dim_kappa([e1]) == 1
        assert dim_kappa([e1, e2, e3]) == 3


class TestMembership:
    def test_membership(self):
        """a₅ is a member under e₁ (τ fires), not under e₂."""
        assert membership(eval_dot, e1, a5) is True
        assert membership(eval_dot, e2, a5) is False


class TestAxioms:
    @pytest.mark.parametrize("d1", range(8))
    @pytest.mark.parametrize("d2", range(8))
    @pytest.mark.parametrize("a", range(8))
    def test_profile_linearity(self, d1, d2, a):
        assert check_profile_linearity(eval_dot, d1, d2, a)

    @pytest.mark.parametrize("d", range(8))
    @pytest.mark.parametrize("y1", range(8))
    @pytest.mark.parametrize("y2", range(8))
    def test_eval_linearity(self, d, y1, y2):
        assert check_eval_linearity(eval_dot, d, y1, y2)

    def test_bilinearity(self):
        assert check_bilinearity(eval_dot, e1, e2, a5, a2)

    def test_operationalist(self):
        """a₀ and a₁ are indistinguishable under κ₂ = ⟨e₁,e₂⟩."""
        kappa_2 = [e1, e2]
        assert check_operationalist(eval_dot, kappa_2, a0, a1)

    def test_operationalist_separated(self):
        """a₀ and a₁ ARE distinguishable under κ₃ = ⟨e₁,e₂,e₃⟩."""
        kappa_3 = [e1, e2, e3]
        assert not check_operationalist(eval_dot, kappa_3, a0, a1)
