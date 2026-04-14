"""Tests for cstz.monoidal."""

import pytest
from cstz.monoidal import tensor_witness, swap_conjugation, cd_mul

e1, e2, e3 = 0b100, 0b010, 0b001

class TestTensor:
    def test_disjoint(self):
        assert tensor_witness(e1, e2) == 0b110
    def test_overlap(self):
        assert tensor_witness(e1, e1) == 0

class TestSwap:
    def test_swap_all(self):
        assert swap_conjugation(0b00) == 0b00  # gap
        assert swap_conjugation(0b01) == 0b10  # σ → τ
        assert swap_conjugation(0b10) == 0b01  # τ → σ
        assert swap_conjugation(0b11) == 0b11  # overlap
    def test_involutive(self):
        for p in range(4):
            assert swap_conjugation(swap_conjugation(p)) == p

class TestCayleyDickson:
    def test_unit(self):
        """(1,0) is the multiplicative unit: (1,0)·x = x."""
        unit = 0b10
        for x in range(4):
            assert cd_mul(unit, x) == x
    def test_zero_divisor(self):
        """(1,0)·(0,1) in CD: Paper App B.39."""
        assert cd_mul(0b10, 0b01) == 0b01
    def test_commutative_step1(self):
        """CD step 1 is commutative (Paper Verification.CDHexagon)."""
        for a in range(4):
            for b in range(4):
                assert cd_mul(a, b) == cd_mul(b, a)
