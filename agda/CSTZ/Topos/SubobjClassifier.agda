------------------------------------------------------------------------
-- CSTZ.Topos.SubobjClassifier
--
-- Paper §9, Thm 9.4: Ω = GF(2)² is a subobject classifier.  [A]
--
-- "For every monomorphism m: S' ↪ A, there exists a unique
-- χ_m: A → Ω such that S' is the pullback of ⊤: 1 → Ω along χ_m."
--
-- The classifying morphism sends a ↦ (τ_d(a), σ_d(a)).
-- Four-valued internal logic: Belnap's FDE.
------------------------------------------------------------------------

module CSTZ.Topos.SubobjClassifier where

open import CSTZ.GF2
open import CSTZ.Framework.Profile
open import CSTZ.Framework.FourCell

open import Data.Product using (_×_ ; _,_)

-- Paper §9, Def 9.3: Ω = GF(2) × GF(2)
Ω : Set
Ω = F × F

-- The four truth values
⊤Ω : Ω      -- true = ordered-τ = (1,0)
⊤Ω = ordered-τ

⊥Ω : Ω      -- false = ordered-σ = (0,1)
⊥Ω = ordered-σ

unknownΩ : Ω  -- gap = (0,0)
unknownΩ = gap

overdetΩ : Ω  -- overlap = (1,1)
overdetΩ = over

-- Negation on Ω: swap components
-- Paper §9: "¬(τ,σ) = (σ,τ)"
¬Ω : Ω → Ω
¬Ω (τ , σ) = (σ , τ)

-- Conjunction on Ω: componentwise multiplication
-- Paper §9: "∧ = componentwise multiplication in GF(2)²"
_∧Ω_ : Ω → Ω → Ω
(τ₁ , σ₁) ∧Ω (τ₂ , σ₂) = (τ₁ ·F τ₂ , σ₁ ·F σ₂)

-- Disjunction on Ω: componentwise maximum
_∨Ω_ : Ω → Ω → Ω
(τ₁ , σ₁) ∨Ω (τ₂ , σ₂) = (τ₁ ∨B τ₂ , σ₁ ∨B σ₂)
  where
    open import Data.Bool.Base using () renaming (_∨_ to _∨B_)

-- Paper §9: Double negation elimination holds: ¬¬(τ,σ) = (τ,σ)
-- But excluded middle fails at the gap: (0,0) ∨ ¬(0,0) = (0,0) ≠ ⊤
