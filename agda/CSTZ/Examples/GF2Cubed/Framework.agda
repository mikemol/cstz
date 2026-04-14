------------------------------------------------------------------------
-- CSTZ.Examples.GF2Cubed.Framework
--
-- Paper App E, §3: Framework definitions instantiated at GF(2)³.
------------------------------------------------------------------------

module CSTZ.Examples.GF2Cubed.Framework where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Vec.Properties
open import CSTZ.Examples.GF2Cubed.Setup

open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Def 3.5: Profile linearity check

-- e₁(a₃ + a₅) = e₁(110) = 1
-- e₁(a₃) + e₁(a₅) = 0 + 1 = 1  ✓
profile-lin-check-1 : eval e₁ (a₃ +V a₅) ≡ eval e₁ a₃ +F eval e₁ a₅
profile-lin-check-1 = refl

-- (e₁ + e₂)(a₅) = e₁(a₅) + e₂(a₅) = 1 + 0 = 1
profile-lin-check-2 : eval (e₁ +V e₂) a₅ ≡ eval e₁ a₅ +F eval e₂ a₅
profile-lin-check-2 = refl

------------------------------------------------------------------------
-- Def 3.9: Residue

-- Under κ₁ = ⟨e₁⟩: a₀ and a₂ have the same e₁-value (both 0).
-- They form a residue pair.
residue-a₀-a₂ : eval e₁ a₀ ≡ eval e₁ a₂
residue-a₀-a₂ = refl

-- Resolve by adding e₂: now e₂(a₀) = 0 ≠ e₂(a₂) = 1.
resolve-a₀-a₂ : eval e₂ a₀ ≡ 𝟘
resolve-a₀-a₂ = refl

resolve-a₀-a₂' : eval e₂ a₂ ≡ 𝟙
resolve-a₀-a₂' = refl

------------------------------------------------------------------------
-- Prop 3.15: Order-independence

-- e₁(a₅) = 1 regardless of whether e₂ is in κ.
order-indep : eval e₁ a₅ ≡ 𝟙
order-indep = refl
