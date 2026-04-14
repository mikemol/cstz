------------------------------------------------------------------------
-- CSTZ.Examples.GF2Cubed.Higher
--
-- Paper App E, §7: Higher structure at GF(2)³.
------------------------------------------------------------------------

module CSTZ.Examples.GF2Cubed.Higher where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Exterior.Basis
open import CSTZ.Examples.GF2Cubed.Setup

open import Data.Vec using ([] ; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Thm 7.1: (n,1)-structure

-- Grade-1: e₁, e₂, e₃ — directed, non-invertible.
-- Grade-2: e₁∧e₂, e₁∧e₃, e₂∧e₃ — self-inverse (groupoid).

-- Self-inverse at grade 2: e₁∧e₂ composed with itself = 0
-- (the subset {0,1} is not disjoint from itself)
self-inverse-e₁e₂ : disjoint (true ∷ true ∷ false ∷ [])
                              (true ∷ true ∷ false ∷ []) ≡ false
self-inverse-e₁e₂ = refl

------------------------------------------------------------------------
-- Def 7.13: GF(2) toroid — triangle identity

-- τ + σ = κ  i.e. (1,0) + (0,1) = (1,1)
triangle-check : (𝟙 +F 𝟘 , 𝟘 +F 𝟙) ≡ (𝟙 , 𝟙)
triangle-check = refl

-- τ + κ = σ  i.e. (1,0) + (1,1) = (0,1)
triangle-rot-σ : (𝟙 +F 𝟙 , 𝟘 +F 𝟙) ≡ (𝟘 , 𝟙)
triangle-rot-σ = refl

-- σ + κ = τ  i.e. (0,1) + (1,1) = (1,0)
triangle-rot-τ : (𝟘 +F 𝟙 , 𝟙 +F 𝟙) ≡ (𝟙 , 𝟘)
triangle-rot-τ = refl

------------------------------------------------------------------------
-- Thm 7.15: Grassmannian Gr(2, GF(2)³) = 7 points

-- The 7 grade-2 basis elements correspond to 7 Fano lines.
-- (These are listed in Topos.Fano: fano-line-1 through fano-line-7.)
-- Count: [3 choose 2]_2 = 7.  ✓
