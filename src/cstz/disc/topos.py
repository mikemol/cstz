"""Topos structure — Ω, Belnap logic, Fano plane, convergence.

Paper §9: "Ω = GF(2)² classifies all single-discriminator subobjects.
The internal logic is four-valued (Belnap FDE)."

Mirrors: agda/CSTZ/Topos/*.agda
"""

from __future__ import annotations

from typing import List, Tuple

from cstz.disc.monoidal import swap_conjugation

# ---------------------------------------------------------------------------
# Subobject classifier Ω = GF(2)² (Paper §9, Thm 9.4)
# ---------------------------------------------------------------------------

TRUE_OMEGA = 0b10     # (1,0) = ordered-τ
FALSE_OMEGA = 0b01    # (0,1) = ordered-σ
UNKNOWN_OMEGA = 0b00  # (0,0) = gap
OVERDET_OMEGA = 0b11  # (1,1) = overlap


def omega_neg(p: int) -> int:
    """Negation: swap τ and σ bits.  Paper §9: ¬(τ,σ) = (σ,τ)."""
    return swap_conjugation(p)


def omega_conj(p: int, q: int) -> int:
    """Conjunction: componentwise AND.  Paper §9: ∧ on Ω."""
    return p & q


def omega_disj(p: int, q: int) -> int:
    """Disjunction: componentwise OR.  Paper §9: ∨ on Ω."""
    return p | q


def dne(p: int) -> int:
    """Double negation elimination: ¬¬p = p.  Always holds on Ω."""
    return omega_neg(omega_neg(p))


# ---------------------------------------------------------------------------
# Fano plane PG(2, GF(2)) (Paper §9, Thm 9.20)
# ---------------------------------------------------------------------------

# 7 nonzero points of GF(2)³ = integers 1..7
FANO_POINTS: List[int] = list(range(1, 8))

# 7 Fano lines: triples (a,b,c) where a ⊕ b = c and a < b < c.
# Each line satisfies a ⊕ b ⊕ c = 0.
FANO_LINES: List[Tuple[int, int, int]] = []
for _a in range(1, 8):
    for _b in range(_a + 1, 8):
        _c = _a ^ _b
        if _c > _b:
            FANO_LINES.append((_a, _b, _c))

# Clean up module namespace
del _a, _b, _c

CONVERGENCE_RATE = 3


def unique_top_form(n: int) -> int:
    """The unique grade-n mask: all n bits set.  Paper §9, Thm 9.15."""
    return (1 << n) - 1


def verify_fano_line(a: int, b: int, c: int) -> bool:
    """Verify a Fano line: a ⊕ b = c (equivalently a ⊕ b ⊕ c = 0)."""
    return a ^ b == c
