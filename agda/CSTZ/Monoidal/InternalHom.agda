------------------------------------------------------------------------
-- CSTZ.Monoidal.InternalHom
--
-- Paper §8, Def 8.11: Internal hom [A,B].  [A]
--
-- [A, B] = { d ∈ κ | τ_d(A) = 1 and σ_d(B) = 1 }
-- A sub-population of κ in the σ-perspective.
------------------------------------------------------------------------

module CSTZ.Monoidal.InternalHom where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Category.Emergent

open import Data.Nat using (ℕ)
open import Data.List using (List ; [] ; _∷_ ; filter)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §8, Def 8.11

-- The internal hom [A,B] in C(S,κ) is the set of discriminators
-- that witness A → B: those d ∈ κ with τ_d(A) = 1 and σ_d(B) = 1.

-- Over our representation: given a list of discriminators (regime κ)
-- and evaluation on population elements a, b (representatives of A, B),
-- the internal hom is the sublist of discriminators that fire on both.

internalHom : ∀ {n} → (GF2Vec n → F) → (GF2Vec n → F)
  → List (GF2Vec n) → List (GF2Vec n)
internalHom evalA evalB κ = filter (λ d → evalA d ∧ evalB d) κ
  where open import Data.Bool.Base using (_∧_)

-- Paper §8, Def 8.12: The evaluation morphism
-- ev: [A,B] ⊗ A → B is the application of a discriminator in [A,B]
-- to an element in A.  It bridges the σ-perspective (hom-space)
-- and the κ-perspective (population).

-- Paper §8, Remark: "Closure is the triangle identity."
-- The three components A⊗B, C, [B,C] stand in the same triadic
-- relationship as κ, σ, τ.  Monoidal closure IS the triangle
-- identity at the morphism level.
