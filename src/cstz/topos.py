"""Topos structure — Ω, Belnap logic, Fano plane, convergence.

Paper §9: "Ω = GF(2)² classifies all single-discriminator subobjects.
The internal logic is four-valued (Belnap FDE)."

Mirrors: agda/CSTZ/Topos/*.agda
"""

from __future__ import annotations

from typing import List, Tuple

from cstz.monoidal import swap_conjugation

# ---------------------------------------------------------------------------
# Subobject classifier Ω = GF(2)² (Paper §9, Thm 9.4)
# ---------------------------------------------------------------------------
#
# Cofibration (STUDY.md §8.3, Python cofiber): the four Ω values and the
# three Belnap operators below are *named* in Python but treated
# structurally in Agda. ``agda/CSTZ/Topos/ProofTheory.agda`` reasons
# about the same values via pattern-match cases rather than as a
# first-class constant family; the properties ``em-fails-at-gap`` and
# friends stand in for the operator semantics. The Python naming makes
# runtime composition direct at the cost of requiring callers to bind
# the meaning of each bit pattern.

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
#
# Cofibration (STUDY.md §8.1, aligned): ``agda/CSTZ/Topos/Fano.agda``
# enumerates seven theorems ``fano-line-1 .. fano-line-7`` for the
# same seven lines; Python's ``FANO_LINES`` list and ``verify_fano_line``
# predicate are the operational form of that enumeration. Because the
# Fano plane over GF(2) has exactly seven lines, the two presentations
# carry the same proof strength.

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
