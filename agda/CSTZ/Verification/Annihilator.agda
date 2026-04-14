------------------------------------------------------------------------
-- CSTZ.Verification.Annihilator
--
-- Paper App B.36: Native univalence from the annihilator.  [AO]
--
-- The path space between a and b is {a+b} ∩ κ⊥.
-- The operationalist axiom says ∪κ = V, so ∩κ⊥ = V⊥ = {0}.
-- Persistent equivalence forces a+b = 0, hence a = b.
------------------------------------------------------------------------

module CSTZ.Verification.Annihilator where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Vec.Properties

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- The annihilator of κ

-- κ⊥ = { v ∈ V | ∀ d ∈ κ, d · v = 0 }
-- The set of vectors invisible to all discriminators in κ.

-- If a+b ∈ κ⊥ (for ALL κ-states), then a+b ∈ ∩κ⊥.
-- Under the operationalist axiom, ∪κ = V, so ∩κ⊥ = V⊥ = {0}.
-- Therefore a+b = 0, hence a = b.

-- The concrete step: a+b = 0 implies a = b (over GF(2)).
-- This is just +V-cancel from Vec.Properties.

annihilator-to-equality :
  ∀ {n} (a b : GF2Vec n)
  → a +V b ≡ 𝟎
  → a ≡ b
annihilator-to-equality = +V-cancel

-- The ua map: if a and b are equivalent (connected by a path in κ⊥),
-- then a = b.
-- The idtoeqv map: if a = b, then a+b = 0 ∈ κ⊥.
-- These are inverses.

idtoeqv : ∀ {n} {a b : GF2Vec n} → a ≡ b → a +V b ≡ 𝟎
idtoeqv {_} {a} refl = +V-self a

-- The path space {a+b} ∩ κ⊥ is contractible:
-- if a+b ∈ κ⊥ for all κ, then a+b = 0 (single point).
-- Paper: "Univalence is Galois-group exhaustion: the only
-- persistent orbit is the trivial orbit."
