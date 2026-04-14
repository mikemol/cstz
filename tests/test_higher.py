"""Tests for cstz.higher."""

import pytest
from cstz.higher import (
    Perspective, TAU_POINT, SIGMA_POINT, KAPPA_POINT,
    triangle_identity, rotate,
)

class TestTriangle:
    def test_identity(self):
        assert triangle_identity()

    def test_all_rotations(self):
        """τ⊕σ=κ, τ⊕κ=σ, σ⊕κ=τ."""
        assert TAU_POINT ^ SIGMA_POINT == KAPPA_POINT
        assert TAU_POINT ^ KAPPA_POINT == SIGMA_POINT
        assert SIGMA_POINT ^ KAPPA_POINT == TAU_POINT

class TestRotate:
    def test_kappa_identity(self):
        for p in range(4):
            assert rotate(Perspective.KAPPA, p) == p

    def test_sigma_rotation(self):
        for p in range(4):
            r = rotate(Perspective.SIGMA, p)
            assert 0 <= r <= 3

    def test_tau_rotation(self):
        for p in range(4):
            r = rotate(Perspective.TAU, p)
            assert 0 <= r <= 3
