------------------------------------------------------------------------
-- CSTZ.Sets.EmptyPairing
--
-- Paper §4, Props 4.17-4.18: Empty set and Pairing.  [Axiom class A]
------------------------------------------------------------------------

module CSTZ.Sets.EmptyPairing where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Nat using (ℕ)

-- Paper §4, Prop 4.17: Empty set
-- A contradictory filter (requiring both τ=1 and τ=0) yields
-- the empty collection.  No discriminator is needed; the
-- empty set is the trivial κ-equivalence class.

-- Paper §4, Prop 4.18: Pairing
-- The pair {a,b} is the κ-equivalence class when a+b ∈ κ⊥
-- (the annihilator of κ).  It is NOT a characteristic function —
-- it's defined by what κ CANNOT distinguish.
--
-- Condition: a and b are indistinguishable under κ, i.e.,
-- for every d ∈ κ, eval d a = eval d b.
-- Equivalently: the difference vector a + b is in κ⊥.

-- The annihilator of a regime κ (list of discriminators):
-- κ⊥ = { v ∈ V | ∀ d ∈ κ, d · v = 0 }
inAnnihilator : ∀ {n} → GF2Vec n → GF2Vec n → F
inAnnihilator d v = d ·V v
  where open CSTZ.Vec using (_·V_)

-- a and b are paired under κ if their difference annihilates κ
isPaired : ∀ {n} → GF2Vec n → GF2Vec n → GF2Vec n → Set
isPaired d a b = inAnnihilator d (a +V b) ≡ 𝟘
  where open import Relation.Binary.PropositionalEquality using (_≡_)
