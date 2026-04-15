"""Directed higher categories — triangle identity, perspectives, toroid.

Paper §7: "κ = σ + τ over GF(2). S₃ symmetry provides directed
structure at multiple levels."

Mirrors: agda/CSTZ/Higher/*.agda
"""

from __future__ import annotations

from enum import IntEnum


class Perspective(IntEnum):
    """Paper §7, Prop 7.11: three perspectives.

    Cofibration (STUDY.md §8.3, Python cofiber): Agda tracks the
    three perspectives structurally (via the S₃ symmetry acting on
    role labels) rather than as a finite enumeration type; the
    Python ``IntEnum`` plus toroid-point constants below give the
    same concept a name and an integer index, so runtime code can
    select a GF(2) matrix by index (see :data:`_PERSPECTIVE_MATRIX`
    and :func:`rotate`) rather than dispatch through a conditional.
    """
    KAPPA = 0
    SIGMA = 1
    TAU = 2


# Toroid points as 2-bit packed ints
# Cofibration (STUDY.md §8.3): Python cofiber — Agda reasons about these
# bit patterns through the triangle identity (τ ⊕ σ = κ) without naming
# the individual points.
TAU_POINT = 0b10    # (1,0)
SIGMA_POINT = 0b01  # (0,1)
KAPPA_POINT = 0b11  # (1,1)


# The three perspective rotations are the fixed-origin automorphisms
# of the toroid.  Each is a GF(2)-linear map on (τ, σ) representable
# as a 2×2 matrix over GF(2); the tuple below packs each matrix as
# four bits [m_ττ m_τσ m_στ m_σσ] so that
#     (τ_out, σ_out) = M · (τ, σ)^T   over GF(2).
# Indexing by ``Perspective`` (an IntEnum) is branchless — the
# selection is a single constant-time integer lookup, and the
# multiply-accumulate below is plain AND (GF(2) ×) plus XOR (GF(2) +)
# on single bits.  See agda/CSTZ/Higher/Perspectives.agda:47
# ("S₃ ⊂ GL(2, GF(2))") for the algebraic justification.
_PERSPECTIVE_MATRIX = (
    0b1001,  # KAPPA  identity                 [[1,0],[0,1]]
    0b0111,  # SIGMA  (τ,σ) ↦ (σ, τ⊕σ)         [[0,1],[1,1]]
    0b1110,  # TAU    (τ,σ) ↦ (τ⊕σ, τ)         [[1,1],[1,0]]
)


def triangle_identity() -> bool:
    """Paper §7, Def 7.9: τ ⊕ σ = κ."""
    return TAU_POINT ^ SIGMA_POINT == KAPPA_POINT


def rotate(persp: Perspective, p: int) -> int:
    """Rotate a 2-bit profile under a perspective change.

    Paper §7, Prop 7.11: the three perspectives are the fixed-origin
    elements of GL(2, GF(2)) ≅ S₃ (see
    ``agda/CSTZ/Higher/Perspectives.agda:47``).  Implemented
    branchlessly as a GF(2) matrix-vector multiply: the matrix is
    selected by integer index into :data:`_PERSPECTIVE_MATRIX`; the
    multiply-accumulate is plain AND (GF(2) ×) plus XOR (GF(2) +)
    on single bits.  No conditional dispatch on ``persp``.
    """
    m = _PERSPECTIVE_MATRIX[persp]
    tau = (p >> 1) & 1
    sigma = p & 1
    tau_out = ((m >> 3) & tau) ^ ((m >> 2) & sigma)
    sigma_out = ((m >> 1) & tau) ^ (m & sigma)
    return (tau_out << 1) | sigma_out
