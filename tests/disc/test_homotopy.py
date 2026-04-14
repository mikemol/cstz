"""Tests for cstz.disc.homotopy."""

import pytest
from cstz.disc.exterior import ext_basis, ext_add
from cstz.disc.homotopy import chain_complex_check, exhaustive_filling, self_inverse_check

N = 3

class TestChainComplex:
    @pytest.mark.parametrize("mask", range(8))
    def test_boundary_squared_basis(self, mask):
        chain_complex_check(N, ext_basis(N, mask))

    def test_boundary_squared_sum(self):
        f = ext_add(ext_basis(N, 0b100), ext_basis(N, 0b110))
        chain_complex_check(N, f)

class TestExhaustiveFilling:
    def test_filling_mask(self):
        """Residue at e₁∧e₂ (mask 0b110) fills to 0b1110 in n+1 dim."""
        c = exhaustive_filling(N, 0b110)
        assert c == 0b1110  # bit 3 set + original

class TestSelfInverse:
    @pytest.mark.parametrize("mask", range(8))
    def test_self_inverse(self, mask):
        self_inverse_check(mask)
