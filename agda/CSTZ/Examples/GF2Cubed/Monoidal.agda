------------------------------------------------------------------------
-- CSTZ.Examples.GF2Cubed.Monoidal
--
-- Paper App E, §8: Monoidal structure at GF(2)³.
------------------------------------------------------------------------

module CSTZ.Examples.GF2Cubed.Monoidal where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Exterior.Basis
open import CSTZ.Examples.GF2Cubed.Setup

open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Def 8.1: Monoidal product

-- e₁ ⊗ e₂ = e₁ ∧ e₂ (disjoint, non-degenerate)
monoidal-prod : e₁ ∪ e₂ ≡ true ∷ true ∷ false ∷ []
monoidal-prod = refl

monoidal-prod-coeff : disjoint e₁ e₂ ≡ true
monoidal-prod-coeff = refl

------------------------------------------------------------------------
-- Strict associativity

-- (e₁ ∪ e₂) ∪ e₃ = e₁ ∪ (e₂ ∪ e₃)
-- Both = (true, true, true)
assoc-lhs : (e₁ ∪ e₂) ∪ e₃ ≡ true ∷ true ∷ true ∷ []
assoc-lhs = refl

assoc-rhs : e₁ ∪ (e₂ ∪ e₃) ≡ true ∷ true ∷ true ∷ []
assoc-rhs = refl

-- Strict: both sides are definitionally equal
strict-assoc : (e₁ ∪ e₂) ∪ e₃ ≡ e₁ ∪ (e₂ ∪ e₃)
strict-assoc = refl

------------------------------------------------------------------------
-- Symmetry: e₁ ∧ e₂ = e₂ ∧ e₁

-- e₁ ∪ e₂ = e₂ ∪ e₁
sym-monoidal : e₁ ∪ e₂ ≡ e₂ ∪ e₁
sym-monoidal = refl
