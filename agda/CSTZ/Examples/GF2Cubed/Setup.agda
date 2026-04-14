------------------------------------------------------------------------
-- CSTZ.Examples.GF2Cubed.Setup
--
-- Paper App E: Setup for the GF(2)³ model.
--
-- Population S = GF(2)³ = {a₀,...,a₇} (8 elements as binary strings).
-- Discriminator space V = GF(2)³ with basis {e₁, e₂, e₃}.
-- Four κ-stages: κ₀ = ∅, κ₁ = ⟨e₁⟩, κ₂ = ⟨e₁,e₂⟩, κ₃ = V.
------------------------------------------------------------------------

module CSTZ.Examples.GF2Cubed.Setup where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)
open import Data.Fin using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Population: the 8 elements of GF(2)³

a₀ : GF2Vec 3   -- 000
a₀ = false ∷ false ∷ false ∷ []

a₁ : GF2Vec 3   -- 001
a₁ = false ∷ false ∷ true ∷ []

a₂ : GF2Vec 3   -- 010
a₂ = false ∷ true ∷ false ∷ []

a₃ : GF2Vec 3   -- 011
a₃ = false ∷ true ∷ true ∷ []

a₄ : GF2Vec 3   -- 100
a₄ = true ∷ false ∷ false ∷ []

a₅ : GF2Vec 3   -- 101
a₅ = true ∷ false ∷ true ∷ []

a₆ : GF2Vec 3   -- 110
a₆ = true ∷ true ∷ false ∷ []

a₇ : GF2Vec 3   -- 111
a₇ = true ∷ true ∷ true ∷ []

------------------------------------------------------------------------
-- Discriminator basis: e₁, e₂, e₃
-- eᵢ(a) = the i-th bit of a (0-indexed)

e₁ : GF2Vec 3
e₁ = true ∷ false ∷ false ∷ []

e₂ : GF2Vec 3
e₂ = false ∷ true ∷ false ∷ []

e₃ : GF2Vec 3
e₃ = false ∷ false ∷ true ∷ []

-- Evaluation: eᵢ(a) = dot product eᵢ · a
-- This is the inner product from Vec.agda.

eval : GF2Vec 3 → GF2Vec 3 → F
eval d a = d ·V a

------------------------------------------------------------------------
-- Verify basis evaluations (Paper App E, Def 3.1)

-- e₁ picks out the first bit
e₁-a₀ : eval e₁ a₀ ≡ 𝟘
e₁-a₀ = refl

e₁-a₄ : eval e₁ a₄ ≡ 𝟙
e₁-a₄ = refl

e₁-a₅ : eval e₁ a₅ ≡ 𝟙
e₁-a₅ = refl

e₁-a₇ : eval e₁ a₇ ≡ 𝟙
e₁-a₇ = refl

-- e₂ picks out the second bit
e₂-a₂ : eval e₂ a₂ ≡ 𝟙
e₂-a₂ = refl

e₂-a₅ : eval e₂ a₅ ≡ 𝟘
e₂-a₅ = refl

-- e₃ picks out the third bit
e₃-a₁ : eval e₃ a₁ ≡ 𝟙
e₃-a₁ = refl

e₃-a₄ : eval e₃ a₄ ≡ 𝟘
e₃-a₄ = refl

------------------------------------------------------------------------
-- Composite discriminators

e₁+e₂ : GF2Vec 3
e₁+e₂ = e₁ +V e₂   -- = (true, true, false)

e₁+e₃ : GF2Vec 3
e₁+e₃ = e₁ +V e₃   -- = (true, false, true)

e₂+e₃ : GF2Vec 3
e₂+e₃ = e₂ +V e₃   -- = (false, true, true)

e₁+e₂+e₃ : GF2Vec 3
e₁+e₂+e₃ = e₁ +V e₂ +V e₃  -- = (true, true, true) = a₇

-- Verify
e₁+e₂-val : e₁+e₂ ≡ true ∷ true ∷ false ∷ []
e₁+e₂-val = refl

e₁+e₂+e₃-val : e₁+e₂+e₃ ≡ a₇
e₁+e₂+e₃-val = refl
