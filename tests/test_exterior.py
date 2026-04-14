"""Tests for cstz.exterior — bitmask-indexed exterior algebra.

Exhaustive verification at n=3: all 8 basis elements, all pairs for
wedge commutativity, all elements for ∂∘∂=0.
"""

import pytest
from cstz.exterior import (
    ext_zero, ext_basis, ext_scalar, ext_add, ext_is_zero,
    ext_wedge, ext_grade, ext_restrict_grade,
    ext_boundary,
    check_wedge_self_zero, check_wedge_comm, check_boundary_squared,
)

N = 3  # GF(2)^3 throughout


class TestConstructors:
    def test_zero(self):
        z = ext_zero(N)
        assert len(z) == 8
        assert all(c == 0 for c in z)

    def test_basis(self):
        e1 = ext_basis(N, 0b100)  # e₁
        assert e1[0b100] == 1
        assert sum(e1) == 1

    def test_scalar(self):
        s = ext_scalar(N, 1)
        assert s[0] == 1
        assert sum(s) == 1

    def test_add_inverse(self):
        f = ext_basis(N, 0b101)
        assert ext_add(f, f) == ext_zero(N)  # f + f = 0


class TestWedge:
    def test_basis_disjoint(self):
        """e₁ ∧ e₂ = e₁₂ (basis at mask 0b110)."""
        e1 = ext_basis(N, 0b100)
        e2 = ext_basis(N, 0b010)
        h = ext_wedge(N, e1, e2)
        assert h[0b110] == 1
        assert sum(h) == 1

    def test_basis_overlap(self):
        """e₁ ∧ e₁ = 0 (mask overlaps)."""
        e1 = ext_basis(N, 0b100)
        h = ext_wedge(N, e1, e1)
        assert ext_is_zero(h)

    def test_triple_wedge(self):
        """e₁ ∧ e₂ ∧ e₃ = top form at mask 0b111."""
        e1 = ext_basis(N, 0b100)
        e2 = ext_basis(N, 0b010)
        e3 = ext_basis(N, 0b001)
        e12 = ext_wedge(N, e1, e2)
        e123 = ext_wedge(N, e12, e3)
        assert e123[0b111] == 1
        assert sum(e123) == 1

    @pytest.mark.parametrize("mask", range(1, 8))
    def test_wedge_self_zero(self, mask):
        """Agda: wedge-self-zero — v ∧ v = 0 for all non-empty masks."""
        check_wedge_self_zero(N, mask)

    def test_wedge_comm_exhaustive(self):
        """Agda: wedge₂-comm — commutativity on all basis pairs."""
        for s in range(8):
            f = ext_basis(N, s)
            for t in range(8):
                g = ext_basis(N, t)
                check_wedge_comm(N, f, g)

    def test_wedge_associative(self):
        """(e₁ ∧ e₂) ∧ e₃ = e₁ ∧ (e₂ ∧ e₃)."""
        e1 = ext_basis(N, 0b100)
        e2 = ext_basis(N, 0b010)
        e3 = ext_basis(N, 0b001)
        lhs = ext_wedge(N, ext_wedge(N, e1, e2), e3)
        rhs = ext_wedge(N, e1, ext_wedge(N, e2, e3))
        assert lhs == rhs


class TestGrade:
    def test_grade_values(self):
        assert ext_grade(0b000) == 0
        assert ext_grade(0b001) == 1
        assert ext_grade(0b011) == 2
        assert ext_grade(0b111) == 3

    def test_restrict_grade(self):
        """Keep only grade-2 part of e₁ + e₁₂."""
        f = ext_add(ext_basis(N, 0b100), ext_basis(N, 0b110))
        g = ext_restrict_grade(N, 2, f)
        assert g[0b110] == 1
        assert g[0b100] == 0  # grade 1, zeroed out

    def test_grade_dimensions(self):
        """Λ(GF(2)³) has dimensions 1,3,3,1 at grades 0,1,2,3."""
        dims = [0, 0, 0, 0]
        for mask in range(8):
            dims[ext_grade(mask)] += 1
        assert dims == [1, 3, 3, 1]


class TestBoundary:
    def test_boundary_grade1(self):
        """∂(e₁) = 1 (the grade-0 unit)."""
        e1 = ext_basis(N, 0b100)
        de1 = ext_boundary(N, e1)
        assert de1[0] == 1  # grade-0 coefficient
        assert sum(de1) == 1

    def test_boundary_grade2(self):
        """∂(e₁∧e₂) = e₁ + e₂.

        Agda: Prop 5.5(ii): ∂(e₁ ∧ e₂) = e₂ + e₁ = e₁ + e₂.
        """
        e12 = ext_basis(N, 0b110)
        de12 = ext_boundary(N, e12)
        assert de12[0b100] == 1  # e₁
        assert de12[0b010] == 1  # e₂
        assert sum(de12) == 2

    def test_boundary_grade3(self):
        """∂(e₁∧e₂∧e₃) = e₂∧e₃ + e₁∧e₃ + e₁∧e₂.

        Agda: dd-explicit from Examples/GF2Cubed/Homotopy.
        """
        e123 = ext_basis(N, 0b111)
        de123 = ext_boundary(N, e123)
        assert de123[0b011] == 1  # e₂∧e₃
        assert de123[0b101] == 1  # e₁∧e₃
        assert de123[0b110] == 1  # e₁∧e₂
        assert sum(de123) == 3

    def test_boundary_grade0(self):
        """∂(scalar) = 0."""
        s = ext_scalar(N, 1)
        ds = ext_boundary(N, s)
        assert ext_is_zero(ds)

    @pytest.mark.parametrize("mask", range(8))
    def test_boundary_squared_zero(self, mask):
        """Agda postulate ∂∘∂≡0 — computed and verified for all basis elements.

        Paper §5, Prop 5.5: "Each (k-2)-cell appears exactly twice.
        Over GF(2), 1+1=0."

        This is the KEY verification: the Agda has this as a postulate;
        here we compute it exhaustively.
        """
        f = ext_basis(N, mask)
        check_boundary_squared(N, f)

    def test_boundary_squared_arbitrary(self):
        """∂∘∂=0 on a non-basis element: e₁ + e₁₂."""
        f = ext_add(ext_basis(N, 0b100), ext_basis(N, 0b110))
        check_boundary_squared(N, f)

    def test_boundary_squared_full(self):
        """∂∘∂=0 on ALL 256 possible exterior elements at n=3."""
        for bits in range(256):
            f = [(bits >> i) & 1 for i in range(8)]
            check_boundary_squared(N, f)
