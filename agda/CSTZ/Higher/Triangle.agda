------------------------------------------------------------------------
-- CSTZ.Higher.Triangle
--
-- Paper §7, Def 7.9: Triangle identity κ = σ + τ.  [Axiom class A]
--
-- "Over GF(2), κ = σ ⊕ τ; any of {κ,σ,τ} can serve as the
-- discrimination regime, with the other two as masks."
------------------------------------------------------------------------

module CSTZ.Higher.Triangle where

open import CSTZ.GF2
open import CSTZ.GF2.Properties

open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- Paper §7, Def 7.9:
-- The triangle identity on GF(2)²: for any (τ,σ),
--   κ = τ + σ
--   τ = κ + σ
--   σ = κ + τ
-- All three are the same equation over GF(2) (since +x = -x).

-- The three non-zero points of GF(2)²
τ-point : F × F
τ-point = (𝟙 , 𝟘)

σ-point : F × F
σ-point = (𝟘 , 𝟙)

κ-point : F × F
κ-point = (𝟙 , 𝟙)

-- The triangle identity: κ = τ + σ  (componentwise xor)
triangle : (𝟙 +F 𝟘 , 𝟘 +F 𝟙) ≡ κ-point
triangle = refl

-- Rotation: τ = κ + σ
triangle-τ : (𝟙 +F 𝟘 , 𝟙 +F 𝟙) ≡ τ-point
triangle-τ = refl

-- Rotation: σ = κ + τ
triangle-σ : (𝟙 +F 𝟙 , 𝟙 +F 𝟘) ≡ σ-point
triangle-σ = refl

-- S₃ symmetry: any permutation of {κ,σ,τ} preserves the identity.
-- This generates the three perspectives (Prop 7.11).
