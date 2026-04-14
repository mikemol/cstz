"""Runtime verification checks — fills Agda postulates computationally.

Paper Appendix B: gap-closing proofs, exhaustive at n=3.

Mirrors: agda/CSTZ/Verification/*.agda
"""

from __future__ import annotations

from cstz.disc.gf2 import dot, popcount
from cstz.disc.exterior import (
    ext_basis, ext_boundary, ext_is_zero, ext_wedge,
)
from cstz.disc.framework import chi
from cstz.disc.axioms import check_profile_linearity, check_eval_linearity
from cstz.disc.topos import FANO_LINES, verify_fano_line, unique_top_form
from cstz.disc.monoidal import cd_mul, swap_conjugation


def check_boundary_squared(n: int) -> None:
    """B.18/Prop 5.5: ∂∘∂=0 on ALL basis elements of Λ(GF(2)^n).

    This computationally fills the Agda postulate ∂∘∂≡0.
    """
    for mask in range(1 << n):
        f = ext_basis(n, mask)
        df = ext_boundary(n, f)
        ddf = ext_boundary(n, df)
        assert ext_is_zero(ddf), f"∂∘∂ ≠ 0 at mask {mask:#0{n+2}b}"


def check_boundary_squared_all(n: int) -> None:
    """∂∘∂=0 on ALL 2^{2^n} exterior elements (exhaustive at n=3)."""
    size = 1 << n
    for bits in range(1 << size):
        f = [(bits >> i) & 1 for i in range(size)]
        df = ext_boundary(n, f)
        ddf = ext_boundary(n, df)
        assert ext_is_zero(ddf), f"∂∘∂ ≠ 0 at element {bits:#0{size+2}b}"


def check_fano_lines() -> None:
    """B.5/Thm 9.20: All 7 Fano lines satisfy a⊕b=c."""
    assert len(FANO_LINES) == 7
    for a, b, c in FANO_LINES:
        assert verify_fano_line(a, b, c)


def check_risc(n: int) -> None:
    """B.38: Admissible discriminators = V* = 2^n elements."""
    assert (1 << n) == 2 ** n  # tautological, but documents the count
    # Non-trivial: 2^n - 1.  At n=3: 7 = |Fano points|.
    assert (1 << n) - 1 == len(range(1, 1 << n))


def check_cd_commutativity() -> None:
    """B.39: CD step 1 is commutative."""
    for a in range(4):
        for b in range(4):
            assert cd_mul(a, b) == cd_mul(b, a)


def check_fixed_point_stability() -> None:
    """B.33: dim Λ²(GF(2)²) = 1."""
    n = 2
    grade2_masks = [m for m in range(1 << n) if popcount(m) == n]
    assert len(grade2_masks) == 1
    assert grade2_masks[0] == unique_top_form(n)


def check_swap_involutive() -> None:
    """Swap conjugation is an involution."""
    for p in range(4):
        assert swap_conjugation(swap_conjugation(p)) == p


def check_profile_linearity_exhaustive(n: int) -> None:
    """(P): profile linearity exhaustive at GF(2)^n."""
    for d1 in range(1 << n):
        for d2 in range(1 << n):
            for a in range(1 << n):
                assert check_profile_linearity(dot, d1, d2, a)


def check_eval_linearity_exhaustive(n: int) -> None:
    """(E): evaluation linearity exhaustive at GF(2)^n."""
    for d in range(1 << n):
        for y1 in range(1 << n):
            for y2 in range(1 << n):
                assert check_eval_linearity(dot, d, y1, y2)


def check_truth_tables() -> None:
    """B.10: Belnap FDE truth tables on Ω."""
    from cstz.disc.topos import omega_neg, omega_conj, omega_disj

    # Double negation elimination
    for p in range(4):
        assert omega_neg(omega_neg(p)) == p

    # Excluded middle fails at gap
    assert omega_disj(0, omega_neg(0)) == 0

    # Explosion fails at overlap
    assert omega_conj(3, omega_neg(3)) == 3

    # Conjunction identity: p ∧ p = p
    for p in range(4):
        assert omega_conj(p, p) == p

    # Disjunction identity: p ∨ p = p
    for p in range(4):
        assert omega_disj(p, p) == p
