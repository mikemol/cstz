"""Set-theoretic consequences of the discrimination framework.

Paper §4: extensionality, Russell exclusion, foundation, pairing,
symmetric difference, power set, infinity, choice.

Mirrors: agda/CSTZ/Sets/*.agda
"""

from __future__ import annotations

from typing import List

from cstz.gf2 import dot, vec_add, popcount
from cstz.framework import EvalFn, Regime


# ---------------------------------------------------------------------------
# Extensionality (Paper §4, Thm 4.2)  [A]
# ---------------------------------------------------------------------------


def kappa_equiv(eval_fn: EvalFn, regime: Regime, a: int, b: int) -> bool:
    """Two elements are κ-equivalent iff every discriminator agrees."""
    return all(eval_fn(d, a) == eval_fn(d, b) for d in regime)


# ---------------------------------------------------------------------------
# Russell exclusion (Paper §4, Thm 4.5)  [AEP]
# ---------------------------------------------------------------------------


def russell_exclusion(eval_fn: EvalFn, d: int) -> None:
    """Assert eval(d, 0) == 0.  Linear maps send 0 to 0.

    The Russell predicate would require eval(d_P, 0) = 1.
    Under evaluation linearity, this is impossible.
    """
    result = eval_fn(d, 0)
    assert result == 0, f"Russell: eval({d:#b}, 0) = {result} ≠ 0"


# ---------------------------------------------------------------------------
# Foundation (Paper §4, Thm 4.13)  [AP]
# ---------------------------------------------------------------------------


def chain_depth_bound(n: int) -> int:
    """Maximum chain depth = dim(V) = n."""
    return n


def link_vector(a: int, b: int) -> int:
    """Link vector v = a ⊕ b for membership chain a ∋ b."""
    return vec_add(a, b)


# ---------------------------------------------------------------------------
# Pairing (Paper §4, Prop 4.18)  [A]
# ---------------------------------------------------------------------------


def in_annihilator(d: int, diff: int) -> bool:
    """d · diff = 0: diff is in the annihilator of d."""
    return dot(d, diff) == 0


def is_paired(eval_fn: EvalFn, regime: Regime, a: int, b: int) -> bool:
    """a and b are paired under κ iff all discriminators agree on them.

    Equivalently: a⊕b ∈ κ⊥ (annihilator of every d in κ).
    """
    diff = vec_add(a, b)
    return all(in_annihilator(d, diff) for d in regime)


# ---------------------------------------------------------------------------
# Symmetric difference (Paper §4, Prop 4.19)  [A]
# ---------------------------------------------------------------------------


def sym_diff_discriminator(d_a: int, d_b: int) -> int:
    """Symmetric difference discriminator: d_A ⊕ d_B."""
    return d_a ^ d_b


# ---------------------------------------------------------------------------
# Power set (Paper §4, Def 4.21)  [A]
# ---------------------------------------------------------------------------


def power_set_bound(n: int) -> int:
    """At most 2^n subcollections under an n-dimensional regime."""
    return 1 << n


# ---------------------------------------------------------------------------
# Choice bound (Paper §4, Thm 4.33)  [A finite / AO infinite]
# ---------------------------------------------------------------------------


def choice_measure(n: int, dim_kappa: int) -> int:
    """Termination measure: m(κ) = dim(V) - dim(κ) = dim(V/κ)."""
    return n - dim_kappa
