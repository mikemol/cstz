"""Monoidal closed structure — tensor product, Cayley-Dickson, closure.

Paper §8: "The monoidal product IS the wedge product applied to
morphism witnesses. Closure is the triangle identity at morphism level."

Mirrors: agda/CSTZ/Monoidal/*.agda
"""

from __future__ import annotations


def tensor_witness(d1: int, d2: int) -> int:
    """Monoidal product: d₁ ∧ d₂ (disjoint union or 0)."""
    return d1 | d2 if (d1 & d2) == 0 else 0


def swap_conjugation(p: int) -> int:
    """Paper §8, Def 8.7: (a,b)* = (b,a) on GF(2)² packed as 2-bit int."""
    return ((p & 1) << 1) | ((p >> 1) & 1)


def cd_mul(a: int, b: int) -> int:
    """Cayley-Dickson multiplication on GF(2)² (2-bit packed ints).

    Paper §8, Def 8.8:
    (a₁,a₂)(b₁,b₂) = (a₁b₁ ⊕ b₂a₂, b₂a₁ ⊕ a₂b₁)
    where conjugation is trivial over GF(2) (since -1=1).
    """
    a1 = (a >> 1) & 1
    a2 = a & 1
    b1 = (b >> 1) & 1
    b2 = b & 1
    r1 = (a1 & b1) ^ (b2 & a2)
    r2 = (b2 & a1) ^ (a2 & b1)
    return (r1 << 1) | r2
