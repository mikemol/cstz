"""GF(2) field and packed-bitvector GF(2)^n operations.

Paper §2: "GF(2) is the field {0,1} with characteristic 2, where
1+1=0 and every element is its own additive inverse."

Representations:
  - GF(2) scalar: int in {0, 1}, addition = ^, multiplication = &
  - GF(2)^n vector: int with n bits, vec_add = ^, dot = popcount(& ) mod 2
  - Standard basis: e_i = 1 << i

Mirrors: agda/CSTZ/GF2.agda, GF2/Properties.agda, Vec.agda, Vec/Properties.agda
"""

from __future__ import annotations

# ---------------------------------------------------------------------------
# GF(2) scalars
# ---------------------------------------------------------------------------

ZERO: int = 0
ONE: int = 1


def gf2_add(a: int, b: int) -> int:
    """Addition in GF(2) = XOR."""
    return a ^ b


def gf2_mul(a: int, b: int) -> int:
    """Multiplication in GF(2) = AND."""
    return a & b


def double_cancel(x: int) -> int:
    """x + x = 0 over GF(2).  The single fact driving half the paper."""
    return x ^ x  # always 0


# ---------------------------------------------------------------------------
# GF(2)^n packed bitvectors
# ---------------------------------------------------------------------------


def popcount(x: int) -> int:
    """Number of set bits."""
    return bin(x).count("1")


def vec_zero() -> int:
    """The zero vector (any dimension)."""
    return 0


def basis(i: int) -> int:
    """Standard basis vector e_i (1 at position i, 0 elsewhere)."""
    return 1 << i


def vec_add(u: int, v: int) -> int:
    """Vector addition over GF(2) = XOR of packed bitvectors."""
    return u ^ v


def dot(u: int, v: int) -> int:
    """Inner product over GF(2): parity of set bits in u & v."""
    return popcount(u & v) & 1


# ---------------------------------------------------------------------------
# Properties (assertion-based; Agda counterparts are proven terms)
# ---------------------------------------------------------------------------


def check_double_cancel(x: int) -> None:
    """Agda: double-cancel / self-inverse."""
    assert double_cancel(x) == 0


def check_vec_self_inverse(v: int) -> None:
    """Agda: +V-self — v + v = 0."""
    assert vec_add(v, v) == 0


def check_bilinear_left(u: int, v: int, w: int) -> None:
    """Agda: ·V-linearˡ — dot(u+v, w) = dot(u,w) ^ dot(v,w)."""
    assert dot(vec_add(u, v), w) == gf2_add(dot(u, w), dot(v, w))


def check_bilinear_right(u: int, v: int, w: int) -> None:
    """Agda: ·V-linearʳ — dot(u, v+w) = dot(u,v) ^ dot(u,w)."""
    assert dot(u, vec_add(v, w)) == gf2_add(dot(u, v), dot(u, w))


def check_linear_map_zero(d: int) -> None:
    """Agda: linear-map-zero — dot(d, 0) = 0.  Key for Russell exclusion."""
    assert dot(d, 0) == 0
