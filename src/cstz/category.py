"""Category theory from discrimination — directed morphisms, 2-category.

Paper §6: "Direction arises from the τ/σ asymmetry. Composition of
1-morphisms produces a 2-cell: g ∘ f = d₁ ∧ d₂ ∈ Λ²V."

Mirrors: agda/CSTZ/Category/*.agda
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum
from typing import Callable, List

from cstz.gf2 import dot, vec_add


@dataclass(frozen=True)
class DirectedMorphism:
    """Paper §6, Def 6.1: a discriminator witnessing a → b."""
    witness: int
    tau_source: int   # must be 1
    sigma_target: int  # must be 1


def compose_witnesses(d1: int, d2: int) -> int:
    """Wedge of two grade-1 elements: d1 | d2 if disjoint, else 0."""
    return d1 | d2 if (d1 & d2) == 0 else 0


def compose_coeff(d1: int, d2: int) -> int:
    """Non-zero iff d1 and d2 are linearly independent (disjoint bits)."""
    return 1 if (d1 & d2) == 0 else 0


def interchange(a: int, b: int, c: int, d: int) -> bool:
    """Paper §6, Thm 6.8: (a^b)^(c^d) == (a^c)^(b^d) over GF(2).

    The interchange law holds because cross-terms cancel via 1+1=0.
    """
    return ((a ^ b) ^ (c ^ d)) == ((a ^ c) ^ (b ^ d))


def equalizer_witness(d_f: int, d_g: int) -> int:
    """Equalizer of f,g: kernel of d_f ⊕ d_g.  Paper §6, Prop 6.20."""
    return d_f ^ d_g


class LimitKind(IntEnum):
    """Paper §6, Prop 6.20: five limit types."""
    TERMINAL = 0
    PRODUCT = 1
    EQUALIZER = 2
    PULLBACK = 3
    GENERAL = 4
