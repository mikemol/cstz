------------------------------------------------------------------------
-- CSTZ.Examples.GF2Cubed.Homotopy
--
-- Paper App E, §5: Homotopical structure at GF(2)³.
------------------------------------------------------------------------

module CSTZ.Examples.GF2Cubed.Homotopy where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Exterior.Basis
open import CSTZ.Examples.GF2Cubed.Setup

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Def 5.2: Discrimination complex Λ(GF(2)³)
-- Dimensions: grade 0 = 1, grade 1 = 3, grade 2 = 3, grade 3 = 1.

-- Grade-0 basis: the empty subset (false,false,false)
g0-basis : Subset 3
g0-basis = false ∷ false ∷ false ∷ []

g0-grade : card g0-basis ≡ 0
g0-grade = refl

-- Grade-1 bases: (T,F,F), (F,T,F), (F,F,T)
-- These are e₁, e₂, e₃ themselves as subsets.

g1-e₁ : card e₁ ≡ 1
g1-e₁ = refl

g1-e₂ : card e₂ ≡ 1
g1-e₂ = refl

g1-e₃ : card e₃ ≡ 1
g1-e₃ = refl

-- Grade-2 bases: (T,T,F), (T,F,T), (F,T,T)
g2-e₁e₂ : Subset 3
g2-e₁e₂ = true ∷ true ∷ false ∷ []

g2-e₁e₃ : Subset 3
g2-e₁e₃ = true ∷ false ∷ true ∷ []

g2-e₂e₃ : Subset 3
g2-e₂e₃ = false ∷ true ∷ true ∷ []

g2-e₁e₂-grade : card g2-e₁e₂ ≡ 2
g2-e₁e₂-grade = refl

g2-e₁e₃-grade : card g2-e₁e₃ ≡ 2
g2-e₁e₃-grade = refl

g2-e₂e₃-grade : card g2-e₂e₃ ≡ 2
g2-e₂e₃-grade = refl

-- Grade-3 basis: (T,T,T)
g3-top : Subset 3
g3-top = true ∷ true ∷ true ∷ []

g3-top-grade : card g3-top ≡ 3
g3-top-grade = refl

------------------------------------------------------------------------
-- Prop 5.5: ∂²(e₁∧e₂∧e₃) = 0

-- ∂(e₁∧e₂∧e₃) = e₂∧e₃ + e₁∧e₃ + e₁∧e₂
-- (remove each of the three factors)

-- ∂²(e₁∧e₂∧e₃) = ∂(e₂∧e₃) + ∂(e₁∧e₃) + ∂(e₁∧e₂)
--               = (e₂+e₃) + (e₁+e₃) + (e₁+e₂)
--               = 2e₁ + 2e₂ + 2e₃ = 0  ✓

-- The explicit computation: each eᵢ appears twice, and 1+1=0.
-- We verify: e₁ + e₁ = 0, e₂ + e₂ = 0, e₃ + e₃ = 0.
dd-cancels-e₁ : e₁ +V e₁ ≡ 𝟎
dd-cancels-e₁ = refl

dd-cancels-e₂ : e₂ +V e₂ ≡ 𝟎
dd-cancels-e₂ = refl

dd-cancels-e₃ : e₃ +V e₃ ≡ 𝟎
dd-cancels-e₃ = refl

-- The full double-boundary: (e₂+e₃) + (e₁+e₃) + (e₁+e₂)
-- = (e₁+e₁) + (e₂+e₂) + (e₃+e₃) = 0+0+0 = 0
dd-explicit : (e₂ +V e₃) +V (e₁ +V e₃) +V (e₁ +V e₂) ≡ 𝟎
dd-explicit = refl

------------------------------------------------------------------------
-- Thm 5.10: Groupoid

-- Commutativity at grade 2: e₁∧e₂ = e₂∧e₁ (same subset)
-- Nilpotency: e₁∧e₂ composed with itself = 0 (subset overlaps)

-- Commutativity witness: e₁ ∪ e₂ = e₂ ∪ e₁
comm-subset : e₁ ∪ e₂ ≡ e₂ ∪ e₁
comm-subset = refl

------------------------------------------------------------------------
-- Prop 5.12: Univalence

-- a₃ + a₅ = 011 + 101 = 110 = e₁ + e₂
univ-diff : a₃ +V a₅ ≡ e₁+e₂
univ-diff = refl

-- e₁ separates them: e₁·a₃ = 0, e₁·a₅ = 1
univ-separated : eval e₁ a₃ ≡ 𝟘
univ-separated = refl

univ-separated' : eval e₁ a₅ ≡ 𝟙
univ-separated' = refl
