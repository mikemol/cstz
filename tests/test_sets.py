"""Tests for cstz.sets — set-theoretic consequences."""

import pytest
from cstz.gf2 import dot
from cstz.sets import (
    kappa_equiv, russell_exclusion, chain_depth_bound, link_vector,
    in_annihilator, is_paired, sym_diff_discriminator,
    power_set_bound, choice_measure,
)

eval_dot = dot
e1, e2, e3 = 0b100, 0b010, 0b001
a0, a1, a2, a3, a4, a5, a6, a7 = range(8)


class TestExtensionality:
    def test_equiv_under_kappa2(self):
        """a₀ and a₁ are κ₂-equivalent (differ only in e₃)."""
        kappa_2 = [e1, e2]
        assert kappa_equiv(eval_dot, kappa_2, a0, a1)

    def test_not_equiv_under_kappa3(self):
        """a₀ and a₁ are NOT κ₃-equivalent."""
        kappa_3 = [e1, e2, e3]
        assert not kappa_equiv(eval_dot, kappa_3, a0, a1)

    def test_all_distinct_under_full(self):
        """Under κ₃=V, all 8 elements are distinct."""
        kappa_3 = [e1, e2, e3]
        for i in range(8):
            for j in range(i + 1, 8):
                assert not kappa_equiv(eval_dot, kappa_3, i, j)


class TestRussell:
    @pytest.mark.parametrize("d", range(8))
    def test_exclusion(self, d):
        """eval(d, 0) = 0 for all d — Russell excluded."""
        russell_exclusion(eval_dot, d)

    def test_russell_violation_raises(self):
        """An affine eval would violate Russell."""
        def affine_eval(d, a):
            return (dot(d, a) ^ 1) & 1  # adds constant 1 = affine
        with pytest.raises(AssertionError, match="Russell"):
            russell_exclusion(affine_eval, e1)


class TestFoundation:
    def test_chain_bound(self):
        assert chain_depth_bound(3) == 3

    def test_link_vectors(self):
        """Chain a₇∋a₃∋a₁: links are e₁, e₂ (independent)."""
        assert link_vector(a7, a3) == e1  # 111^011 = 100
        assert link_vector(a3, a1) == e2  # 011^001 = 010
        assert link_vector(a1, a0) == e3  # 001^000 = 001


class TestPairing:
    def test_paired_a4_a6(self):
        """a₄ and a₆ paired under ⟨e₁,e₃⟩ (differ in e₂ only)."""
        kappa = [e1, e3]
        assert is_paired(eval_dot, kappa, a4, a6)

    def test_not_paired_a0_a4(self):
        """a₀ and a₄ not paired under ⟨e₁,e₃⟩ (e₁ separates)."""
        kappa = [e1, e3]
        assert not is_paired(eval_dot, kappa, a0, a4)

    def test_annihilator(self):
        """a₄⊕a₆ = e₂; e₁·e₂ = 0, e₃·e₂ = 0."""
        diff = a4 ^ a6  # 100 ^ 110 = 010 = e₂
        assert diff == e2
        assert in_annihilator(e1, diff)
        assert in_annihilator(e3, diff)


class TestSymDiff:
    def test_sym_diff(self):
        """(e₁⊕e₂)(a₂) = 1, (e₁⊕e₂)(a₆) = 0."""
        d = sym_diff_discriminator(e1, e2)
        assert dot(d, a2) == 1  # 110·010 = 0+1+0 = 1
        assert dot(d, a6) == 0  # 110·110 = 1+1+0 = 0


class TestPowerSet:
    def test_bound(self):
        assert power_set_bound(2) == 4
        assert power_set_bound(3) == 8


class TestChoice:
    def test_measure(self):
        assert choice_measure(3, 0) == 3
        assert choice_measure(3, 1) == 2
        assert choice_measure(3, 3) == 0
