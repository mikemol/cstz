------------------------------------------------------------------------
-- CSTZ.Sets.BooleanDim
--
-- Paper §4, Def 4.10: Boolean dimension.  [Axiom class A]
--
-- A dimension d is Boolean over S if χ_d(a) = 1 for all a ∈ S.
-- Excluded middle holds locally only where Booleanness is verified.
------------------------------------------------------------------------

module CSTZ.Sets.BooleanDim where

open import CSTZ.GF2
open import CSTZ.Framework.Profile
open import CSTZ.Framework.XOR

-- A discriminator is Boolean over a population if its XOR signature
-- is 1 (discriminated) for every element.
IsBooleanDim : ∀ {S : Set} → (S → Profile) → Set
IsBooleanDim {S} prof = ∀ (a : S) → χ (prof a) ≡ 𝟙
  where open import Relation.Binary.PropositionalEquality using (_≡_)
