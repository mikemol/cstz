"""Exterior algebra Λ(GF(2)^n) — bitmask-indexed tensor representation.

An element of Λ(GF(2)^n) is a list of 2^n GF(2) coefficients, indexed
by n-bit masks.  coeffs[mask] is the coefficient of the basis element
corresponding to the subset encoded by `mask`.

Paper §2: "Λ(GF(2)^n) = ⊕_k Λ^k(GF(2)^n), graded by k from 0 to n."
Paper §5: boundary operator ∂, chain complex ∂∘∂=0.

Operations:
  - Addition: pointwise XOR
  - Wedge product: disjoint-pair convolution (s & t == 0 → h[s|t] ^= 1)
  - Boundary ∂: for each bit i not in t, XOR in f[t | (1<<i)]
  - Grade: popcount of mask

Mirrors: agda/CSTZ/Exterior/{Basis,Wedge,Graded,Boundary}.agda
"""

from __future__ import annotations

from cstz.disc.gf2 import popcount


# ---------------------------------------------------------------------------
# Type alias
# ---------------------------------------------------------------------------

# An exterior element over GF(2)^n: list of 2^n GF(2) coefficients.
# coeffs[mask] = coefficient of basis element indexed by `mask`.
from typing import List
ExteriorElement = List[int]


# ---------------------------------------------------------------------------
# Constructors
# ---------------------------------------------------------------------------


def ext_zero(n: int) -> ExteriorElement:
    """Zero element: all coefficients 0."""
    return [0] * (1 << n)


def ext_basis(n: int, mask: int) -> ExteriorElement:
    """Basis element: 1 at position `mask`, 0 elsewhere."""
    e = ext_zero(n)
    e[mask] = 1
    return e


def ext_scalar(n: int, c: int) -> ExteriorElement:
    """Scalar (grade-0) element: c at mask 0, 0 elsewhere."""
    e = ext_zero(n)
    e[0] = c & 1
    return e


# ---------------------------------------------------------------------------
# Arithmetic
# ---------------------------------------------------------------------------


def ext_add(f: ExteriorElement, g: ExteriorElement) -> ExteriorElement:
    """Addition: pointwise XOR of coefficients."""
    return [a ^ b for a, b in zip(f, g)]


def ext_is_zero(f: ExteriorElement) -> bool:
    """Check if all coefficients are zero."""
    return all(c == 0 for c in f)


# ---------------------------------------------------------------------------
# Wedge product
# ---------------------------------------------------------------------------


def ext_wedge(n: int, f: ExteriorElement, g: ExteriorElement) -> ExteriorElement:
    """Wedge product via disjoint-pair convolution.

    h[s|t] ^= f[s] & g[t]  for all (s,t) with s & t == 0.

    Over GF(2), f[s] & g[t] is 1 iff both are 1.  The XOR accumulates
    because multiple pairs (s,t) may produce the same union s|t.

    Paper §2: "The wedge product is commutative (since -1 = 1),
    associative, and nilpotent on repeated factors (v∧v = 0)."
    """
    size = 1 << n
    h = [0] * size
    for s in range(size):
        if not f[s]:
            continue
        for t in range(size):
            if not g[t]:
                continue
            if (s & t) == 0:
                h[s | t] ^= 1
    return h


# ---------------------------------------------------------------------------
# Grading
# ---------------------------------------------------------------------------


def ext_grade(mask: int) -> int:
    """Grade of a basis element = popcount of its mask."""
    return popcount(mask)


def ext_restrict_grade(n: int, k: int, f: ExteriorElement) -> ExteriorElement:
    """Zero out all coefficients not at grade k."""
    return [c if popcount(m) == k else 0 for m, c in enumerate(f)]


# ---------------------------------------------------------------------------
# Boundary operator ∂
# ---------------------------------------------------------------------------


def ext_boundary(n: int, f: ExteriorElement) -> ExteriorElement:
    """Boundary operator ∂.

    (∂f)[t] = XOR over {i : bit i not set in t} of f[t | (1<<i)].

    Paper §5, Def 5.3: "∂(e_{i₁} ∧ ⋯ ∧ e_{iₖ}) = Σⱼ (omit e_{iⱼ})."

    In bitmask form: removing bit i from mask S gives S ^ (1<<i).
    Equivalently, adding bit i to mask T gives T | (1<<i).  So
    (∂f)[T] sums f over all single-bit extensions of T.
    """
    size = 1 << n
    df = [0] * size
    for t in range(size):
        val = 0
        for i in range(n):
            if not (t & (1 << i)):  # bit i not set in t
                val ^= f[t | (1 << i)]
        df[t] = val
    return df


# ---------------------------------------------------------------------------
# Properties
# ---------------------------------------------------------------------------


def check_wedge_self_zero(n: int, mask: int) -> None:
    """Agda: wedge-self-zero — v ∧ v = 0 for non-empty subsets.

    Paper §5, Def 5.1: "d ∧ d = 0."
    """
    f = ext_basis(n, mask)
    h = ext_wedge(n, f, f)
    assert ext_is_zero(h), f"v∧v ≠ 0 for mask {mask:#0{n+2}b}"


def check_wedge_comm(n: int, f: ExteriorElement, g: ExteriorElement) -> None:
    """Agda: wedge₂-comm — f ∧ g = g ∧ f.

    Paper §2: "The wedge product is commutative (since -1 = 1)."
    """
    fg = ext_wedge(n, f, g)
    gf = ext_wedge(n, g, f)
    assert fg == gf, "wedge not commutative"


def check_boundary_squared(n: int, f: ExteriorElement) -> None:
    """Agda: ∂∘∂≡0 — ∂(∂f) = 0.

    Paper §5, Prop 5.5: "Each (k-2)-cell appears exactly twice in
    the double sum.  Over GF(2), 1+1=0."

    This is a postulate in the Agda; here we compute it.
    """
    df = ext_boundary(n, f)
    ddf = ext_boundary(n, df)
    assert ext_is_zero(ddf), "∂∘∂ ≠ 0"
