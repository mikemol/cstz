"""Tests for cstz.disc.gf2 — GF(2) field and packed bitvector ops.

Every Agda `refl` from Examples/GF2Cubed/Setup becomes an assert here.
Algebraic laws verified by exhaustive enumeration over GF(2) and GF(2)^3.
"""

import pytest
from cstz.disc.gf2 import (
    ZERO, ONE, gf2_add, gf2_mul, double_cancel,
    popcount, vec_zero, basis, vec_add, dot,
    check_double_cancel, check_vec_self_inverse,
    check_bilinear_left, check_bilinear_right, check_linear_map_zero,
)


# ---------------------------------------------------------------------------
# GF(2) scalar tests
# ---------------------------------------------------------------------------

class TestGF2Scalars:
    def test_add_table(self):
        assert gf2_add(0, 0) == 0
        assert gf2_add(0, 1) == 1
        assert gf2_add(1, 0) == 1
        assert gf2_add(1, 1) == 0  # char 2

    def test_mul_table(self):
        assert gf2_mul(0, 0) == 0
        assert gf2_mul(0, 1) == 0
        assert gf2_mul(1, 0) == 0
        assert gf2_mul(1, 1) == 1

    def test_double_cancel(self):
        assert double_cancel(0) == 0
        assert double_cancel(1) == 0

    def test_char2(self):
        """Paper §2: 1+1=0."""
        assert gf2_add(ONE, ONE) == ZERO

    def test_self_inverse(self):
        """Paper §2: every element is its own additive inverse."""
        for x in (0, 1):
            assert gf2_add(x, x) == 0

    def test_idempotent_mul(self):
        """GF(2): x·x = x."""
        for x in (0, 1):
            assert gf2_mul(x, x) == x


# ---------------------------------------------------------------------------
# GF(2)^n packed bitvector tests
# ---------------------------------------------------------------------------

class TestVecOps:
    def test_popcount(self):
        assert popcount(0) == 0
        assert popcount(0b001) == 1
        assert popcount(0b101) == 2
        assert popcount(0b111) == 3
        assert popcount(0b110) == 2

    def test_basis(self):
        assert basis(0) == 0b001
        assert basis(1) == 0b010
        assert basis(2) == 0b100

    def test_vec_zero(self):
        assert vec_zero() == 0

    def test_vec_add(self):
        """Agda: e₁+e₂+e₃ = a₇."""
        e1, e2, e3 = 0b100, 0b010, 0b001
        assert vec_add(vec_add(e1, e2), e3) == 0b111

    def test_vec_add_self(self):
        """v + v = 0 for all v in GF(2)^3."""
        for v in range(8):
            assert vec_add(v, v) == 0

    def test_dot_basis(self):
        """Agda: e₁·a₄ = 1, e₁·a₀ = 0, etc."""
        e1, e2, e3 = 0b100, 0b010, 0b001
        a0, a4, a5, a7 = 0b000, 0b100, 0b101, 0b111
        # e₁ picks out bit 2
        assert dot(e1, a0) == 0
        assert dot(e1, a4) == 1
        assert dot(e1, a5) == 1
        assert dot(e1, a7) == 1
        # e₂ picks out bit 1
        assert dot(e2, 0b010) == 1  # a₂
        assert dot(e2, a5) == 0
        # e₃ picks out bit 0
        assert dot(e3, 0b001) == 1  # a₁
        assert dot(e3, a4) == 0

    def test_dot_composite(self):
        """Agda: profile-lin-check-2 — eval(e₁+e₂, a₅) = eval(e₁,a₅) ^ eval(e₂,a₅)."""
        e1, e2 = 0b100, 0b010
        a5 = 0b101
        assert dot(e1 ^ e2, a5) == (dot(e1, a5) ^ dot(e2, a5))

    def test_dot_commutative(self):
        """dot(u,v) = dot(v,u) for all u,v in GF(2)^3."""
        for u in range(8):
            for v in range(8):
                assert dot(u, v) == dot(v, u)


# ---------------------------------------------------------------------------
# Property checks — exhaustive over GF(2)^3
# ---------------------------------------------------------------------------

class TestProperties:
    @pytest.mark.parametrize("x", [0, 1])
    def test_check_double_cancel(self, x):
        check_double_cancel(x)

    @pytest.mark.parametrize("v", range(8))
    def test_check_vec_self_inverse(self, v):
        check_vec_self_inverse(v)

    @pytest.mark.parametrize("u", range(8))
    @pytest.mark.parametrize("v", range(8))
    @pytest.mark.parametrize("w", range(8))
    def test_check_bilinear_left(self, u, v, w):
        check_bilinear_left(u, v, w)

    @pytest.mark.parametrize("u", range(8))
    @pytest.mark.parametrize("v", range(8))
    @pytest.mark.parametrize("w", range(8))
    def test_check_bilinear_right(self, u, v, w):
        check_bilinear_right(u, v, w)

    @pytest.mark.parametrize("d", range(8))
    def test_check_linear_map_zero(self, d):
        """Agda: linear-map-zero — key for Russell exclusion."""
        check_linear_map_zero(d)
