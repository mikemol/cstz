"""GF(2)³ integration tests — every Agda refl becomes an assert.

Paper Appendix E: "designed to serve as a specification for formal
verification (e.g., in Agda)."

Mirrors: agda/CSTZ/Examples/GF2Cubed/*.agda
"""

import pytest
from cstz.disc.gf2 import dot, vec_add, popcount
from cstz.disc.exterior import (
    ext_basis, ext_add, ext_boundary, ext_is_zero, ext_wedge, ext_grade,
)
from cstz.disc.framework import (
    GAP, ORDERED_SIGMA, ORDERED_TAU, OVER,
    classify, chi, profile, membership,
)
from cstz.disc.sets import kappa_equiv, is_paired, link_vector
from cstz.disc.topos import omega_neg, omega_conj, omega_disj, FANO_LINES
from cstz.disc.examples import *


class TestSetup:
    def test_population_range(self):
        assert POPULATION == list(range(8))

    def test_basis_values(self):
        assert e1 == 0b100
        assert e2 == 0b010
        assert e3 == 0b001

    def test_composites(self):
        assert e1_e2 == 0b110
        assert e1_e2_e3 == 0b111 == a7


class TestFrameworkExamples:
    def test_eval_e1(self):
        """Agda: e₁-a₀, e₁-a₄, e₁-a₅, e₁-a₇."""
        assert eval_dot(e1, a0) == 0
        assert eval_dot(e1, a4) == 1
        assert eval_dot(e1, a5) == 1
        assert eval_dot(e1, a7) == 1

    def test_profile_linearity(self):
        """Agda: profile-lin-check-1 and 2."""
        assert eval_dot(e1, a3 ^ a5) == eval_dot(e1, a3) ^ eval_dot(e1, a5)
        assert eval_dot(e1 ^ e2, a5) == eval_dot(e1, a5) ^ eval_dot(e2, a5)

    def test_residue_detection(self):
        """Agda: residue-a₀-a₂, resolve-a₀-a₂."""
        assert eval_dot(e1, a0) == eval_dot(e1, a2)  # unresolved
        assert eval_dot(e2, a0) != eval_dot(e2, a2)  # resolved by e₂


class TestSetsExamples:
    def test_extensionality(self):
        """All 8 elements distinct under κ₃."""
        for i in range(8):
            for j in range(i + 1, 8):
                assert not kappa_equiv(eval_dot, kappa_3, i, j)

    def test_russell(self):
        """dP(a₀) = 1 + a₀·a₀ = 1. dP(a₀)+dP(a₀) = 0."""
        dp_a0 = 1 ^ (eval_dot(a0, a0))
        assert dp_a0 == 1
        assert dp_a0 ^ dp_a0 == 0  # nonlinear: dP(0+0)=1 ≠ dP(0)+dP(0)=0

    def test_pairing_a4_a6(self):
        """Agda: pairing-diff, pair-annihilator-e₁, e₃."""
        assert a4 ^ a6 == e2
        kappa = [e1, e3]
        assert is_paired(eval_dot, kappa, a4, a6)

    def test_foundation_chain(self):
        """Agda: link-v₁, link-v₂, link-v₃."""
        assert link_vector(a7, a3) == e1
        assert link_vector(a3, a1) == e2
        assert link_vector(a1, a0) == e3

    def test_choice(self):
        """Agda: choice-unresolved then choice-resolved."""
        assert eval_dot(e1, a0) == eval_dot(e1, a1)  # unresolved in S₁
        assert eval_dot(e1, a4) == eval_dot(e1, a5)  # unresolved in S₂
        assert eval_dot(e3, a0) != eval_dot(e3, a1)  # resolved by e₃
        assert eval_dot(e3, a4) != eval_dot(e3, a5)  # resolved by e₃

    def test_indistinguishability(self):
        """Agda: indist-diff — a₀+a₁ = e₃ ∈ κ₂⊥."""
        assert a0 ^ a1 == e3
        assert kappa_equiv(eval_dot, kappa_2, a0, a1)


class TestHomotopyExamples:
    def test_complex_dimensions(self):
        """Λ(GF(2)³) has grade dimensions 1,3,3,1."""
        dims = [0] * 4
        for mask in range(8):
            dims[ext_grade(mask)] += 1
        assert dims == [1, 3, 3, 1]

    def test_boundary_e12(self):
        """∂(e₁∧e₂) = e₁ + e₂."""
        de12 = ext_boundary(3, ext_basis(3, 0b110))
        assert de12[0b100] == 1 and de12[0b010] == 1

    def test_boundary_squared_e123(self):
        """∂²(e₁∧e₂∧e₃) = 0 (explicit)."""
        e123 = ext_basis(3, 0b111)
        de123 = ext_boundary(3, e123)
        dde123 = ext_boundary(3, de123)
        assert ext_is_zero(dde123)

    def test_wedge_comm(self):
        """e₁∧e₂ = e₂∧e₁."""
        fg = ext_wedge(3, ext_basis(3, e1), ext_basis(3, e2))
        gf = ext_wedge(3, ext_basis(3, e2), ext_basis(3, e1))
        assert fg == gf


class TestCategoryExamples:
    def test_four_classes(self):
        """C(S,κ₂) has 4 equivalence classes: A,B,C,D."""
        classes = {}
        for elem in range(8):
            key = (eval_dot(e1, elem), eval_dot(e2, elem))
            classes.setdefault(key, []).append(elem)
        assert len(classes) == 4
        assert classes[(0, 0)] == [a0, a1]  # A
        assert classes[(0, 1)] == [a2, a3]  # B
        assert classes[(1, 0)] == [a4, a5]  # C
        assert classes[(1, 1)] == [a6, a7]  # D


class TestToposExamples:
    def test_omega_dne(self):
        for p in range(4):
            assert omega_neg(omega_neg(p)) == p

    def test_em_fails_gap(self):
        assert omega_disj(0, omega_neg(0)) == 0

    def test_fano_all_lines(self):
        for a, b, c in FANO_LINES:
            assert a ^ b == c

    def test_galois_order(self):
        """GL(3,GF(2)) = 168."""
        # |GL(3,GF(2))| = (2³-1)(2³-2)(2³-4) = 7·6·4 = 168
        assert (8 - 1) * (8 - 2) * (8 - 4) == 168


class TestCycleExamples:
    def test_2cycle_link(self):
        """a₃⊕a₅ = e₁+e₂."""
        assert a3 ^ a5 == e1_e2

    def test_3cycle_closes(self):
        """(e₂+e₃) + e₃ + e₂ = 0."""
        assert (e2 ^ e3) ^ e3 ^ e2 == 0

    def test_chain_cycle_indep(self):
        """Chain link e₁ and cycle link e₁+e₂ are independent."""
        assert e1 ^ e1_e2 == e2  # nonzero → independent
