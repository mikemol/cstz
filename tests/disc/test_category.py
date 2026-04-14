"""Tests for cstz.disc.category."""

import pytest
from cstz.disc.category import (
    compose_witnesses, compose_coeff, interchange, equalizer_witness, LimitKind,
)

e1, e2, e3 = 0b100, 0b010, 0b001

class TestComposition:
    def test_disjoint(self):
        assert compose_witnesses(e1, e2) == 0b110
        assert compose_coeff(e1, e2) == 1

    def test_overlap(self):
        assert compose_witnesses(e1, e1) == 0
        assert compose_coeff(e1, e1) == 0

    def test_triple(self):
        e12 = compose_witnesses(e1, e2)
        assert compose_witnesses(e12, e3) == 0b111

class TestInterchange:
    @pytest.mark.parametrize("a", range(8))
    @pytest.mark.parametrize("b", range(8))
    @pytest.mark.parametrize("c", range(8))
    @pytest.mark.parametrize("d", range(8))
    def test_interchange_exhaustive(self, a, b, c, d):
        assert interchange(a, b, c, d)

class TestEqualizer:
    def test_equalizer(self):
        assert equalizer_witness(e1, e2) == e1 ^ e2  # 0b110

class TestLimitKind:
    def test_values(self):
        assert LimitKind.TERMINAL == 0
        assert LimitKind.GENERAL == 4
