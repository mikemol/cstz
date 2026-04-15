------------------------------------------------------------------------
-- CSTZ.Axiom.EvalLinearity
--
-- Axiom (E): Evaluation linearity.
--
-- Paper §4, Def 4.6: "each τ_x is a GF(2)-linear functional on V"
--
-- When the population S contains elements that are also
-- discriminators (S ∩ V ≠ ∅), the evaluation function is also
-- linear in the second (population) argument.  Together with
-- profile linearity (P), this makes the profile pairing
-- B(x,y) = eval(x)(y) a bilinear form over GF(2).
--
-- Axiom class: AEP.  6 formal objects depend on P+E together.
--
-- Python cofibration (STUDY.md §8.1, P2):
--   * Per-call witness:  src/cstz/axioms.py :: check_eval_linearity
--   * Proof-schema at n: src/cstz/verification.py ::
--                        check_eval_linearity_exhaustive
--   Uniform-vs-parameterized analog of P1; the bundled bilinearity
--   check (src/cstz/axioms.py :: check_bilinearity) is a Python
--   cofiber — Agda derives bilinearity from P1 ∧ P2 by composition
--   without naming the conjunction.
------------------------------------------------------------------------

module CSTZ.Axiom.EvalLinearity where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  eval-linearity :
    ∀ {n : ℕ}
      (eval : GF2Vec n → GF2Vec n → F)
      (d : GF2Vec n) (y₁ y₂ : GF2Vec n)
    → eval d (y₁ +V y₂) ≡ eval d y₁ +F eval d y₂
