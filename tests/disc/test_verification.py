"""Tests for cstz.disc.verification — exhaustive runtime checks."""

import pytest
from cstz.disc.verification import (
    check_boundary_squared,
    check_boundary_squared_all,
    check_fano_lines,
    check_risc,
    check_cd_commutativity,
    check_fixed_point_stability,
    check_swap_involutive,
    check_truth_tables,
)


class TestVerification:
    def test_boundary_squared_n3(self):
        """∂∘∂=0 on all 8 basis elements of Λ(GF(2)³)."""
        check_boundary_squared(3)

    def test_boundary_squared_all_n3(self):
        """∂∘∂=0 on ALL 256 exterior elements of Λ(GF(2)³)."""
        check_boundary_squared_all(3)

    def test_boundary_squared_n2(self):
        """∂∘∂=0 at n=2 (4 basis elements)."""
        check_boundary_squared(2)

    def test_boundary_squared_n1(self):
        """∂∘∂=0 at n=1 (2 basis elements)."""
        check_boundary_squared(1)

    def test_fano_lines(self):
        check_fano_lines()

    def test_risc_n3(self):
        check_risc(3)

    def test_cd_commutativity(self):
        check_cd_commutativity()

    def test_fixed_point_stability(self):
        check_fixed_point_stability()

    def test_swap_involutive(self):
        check_swap_involutive()

    def test_truth_tables(self):
        check_truth_tables()
