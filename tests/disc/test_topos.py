"""Tests for cstz.disc.topos."""

import pytest
from cstz.disc.topos import (
    TRUE_OMEGA, FALSE_OMEGA, UNKNOWN_OMEGA, OVERDET_OMEGA,
    omega_neg, omega_conj, omega_disj, dne,
    FANO_POINTS, FANO_LINES, CONVERGENCE_RATE,
    unique_top_form, verify_fano_line,
)


class TestOmega:
    def test_neg(self):
        assert omega_neg(TRUE_OMEGA) == FALSE_OMEGA
        assert omega_neg(FALSE_OMEGA) == TRUE_OMEGA
        assert omega_neg(UNKNOWN_OMEGA) == UNKNOWN_OMEGA
        assert omega_neg(OVERDET_OMEGA) == OVERDET_OMEGA

    def test_dne(self):
        """Double negation elimination holds for all four values."""
        for p in range(4):
            assert dne(p) == p

    def test_conj(self):
        assert omega_conj(TRUE_OMEGA, FALSE_OMEGA) == UNKNOWN_OMEGA
        assert omega_conj(OVERDET_OMEGA, TRUE_OMEGA) == TRUE_OMEGA

    def test_disj(self):
        assert omega_disj(TRUE_OMEGA, FALSE_OMEGA) == OVERDET_OMEGA
        assert omega_disj(UNKNOWN_OMEGA, TRUE_OMEGA) == TRUE_OMEGA

    def test_em_fails_at_gap(self):
        """Excluded middle fails: gap ∨ ¬gap = gap."""
        p = UNKNOWN_OMEGA
        assert omega_disj(p, omega_neg(p)) == UNKNOWN_OMEGA

    def test_em_at_boolean(self):
        """EM at Boolean states gives overlap, not true."""
        assert omega_disj(TRUE_OMEGA, omega_neg(TRUE_OMEGA)) == OVERDET_OMEGA
        assert omega_disj(FALSE_OMEGA, omega_neg(FALSE_OMEGA)) == OVERDET_OMEGA

    def test_explosion_fails_at_overlap(self):
        """p ∧ ¬p at overlap = overlap (explosion fails)."""
        assert omega_conj(OVERDET_OMEGA, omega_neg(OVERDET_OMEGA)) == OVERDET_OMEGA

    def test_explosion_at_boolean(self):
        """p ∧ ¬p at Boolean = gap (classical)."""
        assert omega_conj(TRUE_OMEGA, omega_neg(TRUE_OMEGA)) == UNKNOWN_OMEGA


class TestFano:
    def test_seven_points(self):
        assert FANO_POINTS == [1, 2, 3, 4, 5, 6, 7]

    def test_seven_lines(self):
        assert len(FANO_LINES) == 7

    def test_all_lines_valid(self):
        for a, b, c in FANO_LINES:
            assert verify_fano_line(a, b, c), f"Line ({a},{b},{c}) fails"

    def test_line_closure(self):
        """Each line satisfies a ⊕ b ⊕ c = 0."""
        for a, b, c in FANO_LINES:
            assert a ^ b ^ c == 0

    def test_convergence_rate(self):
        assert CONVERGENCE_RATE == 3


class TestFixedPoint:
    def test_unique_top_form(self):
        assert unique_top_form(2) == 0b11
        assert unique_top_form(3) == 0b111
