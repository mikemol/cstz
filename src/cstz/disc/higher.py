"""Directed higher categories — triangle identity, perspectives, toroid.

Paper §7: "κ = σ + τ over GF(2). S₃ symmetry provides directed
structure at multiple levels."

Mirrors: agda/CSTZ/Higher/*.agda
"""

from __future__ import annotations

from enum import IntEnum


class Perspective(IntEnum):
    """Paper §7, Prop 7.11: three perspectives."""
    KAPPA = 0
    SIGMA = 1
    TAU = 2


# Toroid points as 2-bit packed ints
TAU_POINT = 0b10    # (1,0)
SIGMA_POINT = 0b01  # (0,1)
KAPPA_POINT = 0b11  # (1,1)


def triangle_identity() -> bool:
    """Paper §7, Def 7.9: τ ⊕ σ = κ."""
    return TAU_POINT ^ SIGMA_POINT == KAPPA_POINT


def rotate(persp: Perspective, p: int) -> int:
    """Rotate a 2-bit profile under a perspective change.

    Paper §7, Prop 7.11: lossless rotation (XOR is involutive).
    """
    tau = (p >> 1) & 1
    sigma = p & 1
    if persp == Perspective.KAPPA:
        return p
    elif persp == Perspective.SIGMA:
        return (sigma << 1) | (tau ^ sigma)
    else:  # TAU
        return ((tau ^ sigma) << 1) | tau
