"""Runtime validators for the three postulated axioms.

Paper §1 (Def 1.1), §3 (Def 3.5), §4 (Def 4.6):
  (P) Profile linearity: eval(d₁⊕d₂, a) = eval(d₁,a) ⊕ eval(d₂,a)
  (E) Evaluation linearity: eval(d, y₁⊕y₂) = eval(d,y₁) ⊕ eval(d,y₂)
  (O) Operationalist: if no discriminator separates a from b, then a = b

Mirrors: agda/CSTZ/Axiom/{ProfileLinearity,EvalLinearity,Operationalist}.agda
"""

from __future__ import annotations

from typing import Callable

EvalFn = Callable[[int, int], int]


def check_profile_linearity(eval_fn: EvalFn, d1: int, d2: int, a: int) -> bool:
    """Axiom (P): eval(d1^d2, a) == eval(d1,a) ^ eval(d2,a).

    Cofibration (STUDY.md §8.1, P1): paired with
    ``agda/CSTZ/Axiom/ProfileLinearity.agda:26``. This function is a
    single-point check; :func:`cstz.verification.check_profile_linearity_exhaustive`
    sweeps all (d1, d2, a) ∈ GF(2)^n — a proof at that n under the
    operationalist reading (exhaustion on a finite population is proof).
    Agda's postulate is uniform in n; Python is a proof-schema over n.
    """
    return eval_fn(d1 ^ d2, a) == (eval_fn(d1, a) ^ eval_fn(d2, a))


def check_eval_linearity(eval_fn: EvalFn, d: int, y1: int, y2: int) -> bool:
    """Axiom (E): eval(d, y1^y2) == eval(d,y1) ^ eval(d,y2).

    Cofibration (STUDY.md §8.1, P2): paired with
    ``agda/CSTZ/Axiom/EvalLinearity.agda:27``. Uniform-vs-schema analog
    of (P); see :func:`cstz.verification.check_eval_linearity_exhaustive`.
    """
    return eval_fn(d, y1 ^ y2) == (eval_fn(d, y1) ^ eval_fn(d, y2))


def check_bilinearity(eval_fn: EvalFn, d1: int, d2: int, y1: int, y2: int) -> bool:
    """Both (P) and (E) hold: the eval pairing is bilinear.

    Cofibration (STUDY.md §8.3): Python cofiber — Agda derives bilinearity
    from P1 ∧ P2 by composition without naming the conjunction; Python
    bundles it as a first-class check.
    """
    return (check_profile_linearity(eval_fn, d1, d2, y1)
            and check_eval_linearity(eval_fn, d1, y1, y2))


def check_operationalist(
    eval_fn: EvalFn, regime: list, a: int, b: int
) -> bool:
    """Axiom (O): if no discriminator in regime separates a from b,
    then a should equal b.  Returns True if the antecedent holds
    (i.e., they are indeed indistinguishable).

    Cofibration (STUDY.md §8.1, P3): this function only witnesses the
    *antecedent* of ``agda/CSTZ/Axiom/Operationalist.agda:26``. The
    axiom's *conclusion* — the equivalence relation ``a ≡ b`` itself —
    is constructively realized by :func:`cstz.sets.kappa_equiv` (regime
    sweep) and :func:`cstz.sets.is_paired` (residue + annihilator).
    The only residual asymmetry with Agda is substitutability: Agda's
    propositional ``≡`` propagates automatically through contexts;
    Python callers must invoke ``kappa_equiv`` at each comparison site.
    """
    return all(eval_fn(d, a) == eval_fn(d, b) for d in regime)
