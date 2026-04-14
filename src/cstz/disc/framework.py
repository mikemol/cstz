"""Discrimination framework — profiles, four-cell, regimes, membership.

Paper §3: "A discriminator is a grade-1 element d ∈ Λ¹V paired with
a predicate d: S → GF(2).  The membership profile is (τ(a), σ(a))
∈ GF(2)².  χ(a) = τ(a)+σ(a) is the XOR signature."

Representations use packed 2-bit ints for profiles/Ω:
  GAP=0b00, ORDERED_SIGMA=0b01, ORDERED_TAU=0b10, OVER=0b11.

Mirrors: agda/CSTZ/Framework/{Discriminator,Profile,FourCell,XOR,
         Regime,Membership,WriteRead}.agda
"""

from __future__ import annotations

from enum import IntEnum
from typing import Callable, List

from cstz.disc.gf2 import dot, vec_add


# ---------------------------------------------------------------------------
# Four-cell structure (Paper §3, Remark 3.4)
# ---------------------------------------------------------------------------

# Profile as 2-bit packed int: tau in bit 1, sigma in bit 0.
GAP = 0b00            # (0,0) — neither predicate fires
ORDERED_SIGMA = 0b01  # (0,1) — σ fires, τ silent
ORDERED_TAU = 0b10    # (1,0) — τ fires, σ silent
OVER = 0b11           # (1,1) — both fire


class CellKind(IntEnum):
    """The four membership cells."""
    GAP = 0
    ORDERED_SIGMA = 1
    ORDERED_TAU = 2
    OVER = 3


def classify(profile: int) -> CellKind:
    """Classify a 2-bit profile into its cell kind."""
    return CellKind(profile & 0b11)


# ---------------------------------------------------------------------------
# XOR signature and residue (Paper §3, Def 3.6-3.9)
# ---------------------------------------------------------------------------


def chi(profile: int) -> int:
    """XOR signature: χ = τ ⊕ σ.  1 = discriminated, 0 = residue."""
    return ((profile >> 1) ^ profile) & 1


def is_residue(profile: int) -> bool:
    """χ = 0: gap or overlap — triggers κ-evolution."""
    return chi(profile) == 0


def is_boolean(profile: int) -> bool:
    """χ = 1: ordered-τ or ordered-σ — stable Boolean state."""
    return chi(profile) == 1


# ---------------------------------------------------------------------------
# Profile computation (Paper §3, Def 3.3)
# ---------------------------------------------------------------------------

# An eval function maps (discriminator, element) → GF(2).
EvalFn = Callable[[int, int], int]


def profile(eval_fn: EvalFn, d_tau: int, d_sigma: int, a: int) -> int:
    """Compute the 2-bit membership profile (τ, σ) of element a.

    τ = eval(d_tau, a), σ = eval(d_sigma, a).
    Returns packed: (τ << 1) | σ.
    """
    return (eval_fn(d_tau, a) << 1) | eval_fn(d_sigma, a)


# ---------------------------------------------------------------------------
# Discrimination regime (Paper §3, Def 3.7-3.8)
# ---------------------------------------------------------------------------

Regime = List[int]  # list of discriminator bitvectors


def evolve(regime: Regime, d: int) -> Regime:
    """κ-evolution: append one discriminator."""
    return regime + [d]


def dim_kappa(regime: Regime) -> int:
    """Dimension of κ = number of discriminators."""
    return len(regime)


# ---------------------------------------------------------------------------
# Membership (Paper §3, Def 3.12)
# ---------------------------------------------------------------------------


def membership(eval_fn: EvalFn, d_tau: int, a: int) -> bool:
    """a ∈_{d_τ} S iff τ_d(a) = 1.  Ternary membership."""
    return eval_fn(d_tau, a) == 1
