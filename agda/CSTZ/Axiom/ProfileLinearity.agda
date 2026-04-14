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
