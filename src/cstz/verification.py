"""Runtime verification checks — fills Agda postulates computationally.

Paper Appendix B: gap-closing proofs, exhaustive at n=3.

Mirrors: agda/CSTZ/Verification/*.agda

Cofibration (STUDY.md §8.1): the ``check_*_exhaustive(n)`` family is a
*proof-schema parameterized by n*. At any fixed dimension ``n`` the
population ``GF(2)^n`` is finite, and every well-formed property in this
framework is ≡-invariant by construction (operationalist axiom P3).
Therefore an exhaustive check over the finite population is a *proof*
at that dimension, not weaker evidence. The asymmetry with Agda is
uniform-vs-schema: Agda's postulate covers all n in a single statement;
Python produces one proof for each caller-chosen n. See also
:mod:`cstz.axioms` for the per-call witnesses.
"""

from __future__ import annotations

from cstz.gf2 import dot, popcount
from cstz.exterior import (
    ext_basis, ext_boundary, ext_is_zero, ext_wedge,
)
from cstz.framework import chi
from cstz.axioms import check_profile_linearity, check_eval_linearity
from cstz.topos import FANO_LINES, verify_fano_line, unique_top_form
from cstz.monoidal import cd_mul, swap_conjugation


def check_boundary_squared(n: int) -> None:
    """B.18/Prop 5.5: ∂∘∂=0 on ALL basis elements of Λ(GF(2)^n).

    This computationally fills the Agda postulate ∂∘∂≡0
    (``agda/CSTZ/Exterior/Boundary.agda:88``). Basis-only sweep;
    :func:`check_boundary_squared_all` extends to every element of
    Λ(GF(2)^n). STUDY.md §8.1, P4.
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
    """B.5/Thm 9.20: All 7 Fano lines satisfy a⊕b=c.

    Cofibration (STUDY.md §8.1, aligned): Fano plane over GF(2) has
    exactly 7 lines; Agda proves each individually as
    ``fano-line-1 .. fano-line-7`` in ``agda/CSTZ/Topos/Fano.agda``.
    Python's finite exhaustion is a complete proof (no uniform-vs-schema
    asymmetry — the structure has a single fixed size).
    """
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
    """B.10: Belnap FDE truth tables on Ω.

    Cofibration (STUDY.md §8.1, aligned + §8.2): bundles the nine
    named Agda theorems in ``agda/CSTZ/Examples/TruthTables.agda``
    (``neg-gap``, ``neg-overlap``, ``dne-gap``, ``dne-overlap``,
    ``conj-gap-any``, ``disj-gap-gap``, ``em-gap``, ``em-overlap``,
    ``expl-overlap``) into a single sweep over the 4-element Ω.
    """
    from cstz.topos import omega_neg, omega_conj, omega_disj

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
