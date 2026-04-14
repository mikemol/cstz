"""Homotopical structure — chain complex, exhaustivity, groupoid.

Paper §5: "∂∘∂=0 entails every residue specifies its own shape."

Mirrors: agda/CSTZ/Homotopy/*.agda
"""

from __future__ import annotations

from cstz.exterior import (
    ExteriorElement, ext_zero, ext_basis, ext_add, ext_is_zero,
    ext_wedge, ext_boundary, ext_grade, ext_restrict_grade,
)


def chain_complex_check(n: int, f: ExteriorElement) -> None:
    """Assert ∂(∂f) = 0.  Paper §5, Prop 5.5."""
    df = ext_boundary(n, f)
    ddf = ext_boundary(n, df)
    assert ext_is_zero(ddf), "∂∘∂ ≠ 0"


def exhaustive_filling(n: int, residue_mask: int) -> int:
    """Fill a residue R by wedging with e_{n}: C = R ∧ e_n.

    The filling lives at mask residue_mask | (1 << n) in Λ(GF(2)^{n+1}).
    ∂C contains R as a component.

    Paper §5, Thm 5.7: "κ-evolution itself IS the constructive filling."
    """
    return residue_mask | (1 << n)


def self_inverse_check(mask: int) -> None:
    """Agda: self-inverse — mask XOR mask = 0."""
    assert mask ^ mask == 0
