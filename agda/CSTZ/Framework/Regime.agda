------------------------------------------------------------------------
-- CSTZ.Framework.Regime
--
-- Paper §3, Def 3.7-3.8: Discrimination regime κ and κ-evolution.
--
-- A regime is parameterized by the discrimination system.
-- κ-evolution appends one discriminator; dimension grows by 1.
------------------------------------------------------------------------

module CSTZ.Framework.Regime where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
open import Data.List using (List ; [] ; _∷_ ; length ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

------------------------------------------------------------------------
-- A regime over GF(2)^n is a list of discriminators (vectors).

Regime : ℕ → Set
Regime n = List (GF2Vec n)

dim-κ : ∀ {n} → Regime n → ℕ
dim-κ = length

------------------------------------------------------------------------
-- κ-evolution: append one discriminator

evolve : ∀ {n} → Regime n → GF2Vec n → Regime n
evolve κ d = κ ++ (d ∷ [])

-- Paper §3, Prop 3.6: Monotonicity — dim grows by exactly 1
evolve-dim : ∀ {n} (κ : Regime n) (d : GF2Vec n)
  → length (evolve κ d) ≡ suc (length κ)
evolve-dim []      d = refl
evolve-dim (x ∷ κ) d = cong suc (evolve-dim κ d)

------------------------------------------------------------------------
-- Sub-regime: dimension ordering

_⊆κ_ : ∀ {n} → Regime n → Regime n → Set
κ₁ ⊆κ κ₂ = length κ₁ ≤ length κ₂
