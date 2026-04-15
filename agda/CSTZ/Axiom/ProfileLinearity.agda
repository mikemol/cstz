------------------------------------------------------------------------
-- CSTZ.Axiom.ProfileLinearity
--
-- Axiom (P): Profile linearity.
--
-- Paper §3, Def 3.5: "(d₁+d₂)(a) = d₁(a)+d₂(a)"
--
-- The map from discriminators to their predicates is GF(2)-linear.
-- This is a structural axiom: it excludes affine predicates
-- (including Russell's) and enables the bilinear form that
-- underlies most of the framework.
--
-- Axiom class: AP.  9 formal objects depend on this.
--
-- Python cofibration (STUDY.md §8.1, P1):
--   * Per-call witness:  src/cstz/axioms.py :: check_profile_linearity
--   * Proof-schema at n: src/cstz/verification.py ::
--                        check_profile_linearity_exhaustive
--   Uniform-vs-parameterized: Agda proves once for all n; Python
--   produces a complete proof at each caller-chosen n (finite
--   population, every well-formed property is ≡-invariant).
------------------------------------------------------------------------

module CSTZ.Axiom.ProfileLinearity where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  profile-linearity :
    ∀ {n : ℕ} {S : Set}
      (eval : GF2Vec n → S → F)
      (d₁ d₂ : GF2Vec n) (a : S)
    → eval (d₁ +V d₂) a ≡ eval d₁ a +F eval d₂ a
