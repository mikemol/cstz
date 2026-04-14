------------------------------------------------------------------------
-- CSTZ.Homotopy.Univalence
--
-- Paper §5, Prop 5.12: Univalence as extensionality.  [Axiom class AO]
--
-- "Two κ-equivalence classes that cannot be distinguished by any
-- discriminator are equal as types.  The path space is contractible."
--
-- The operationalist axiom makes this concrete: persistent
-- equivalence (a + b ∈ ∩κ⊥) forces a + b = 0, hence a = b.
-- Univalence is Galois-group exhaustion.
------------------------------------------------------------------------

module CSTZ.Homotopy.Univalence where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Axiom.Operationalist

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)

-- Paper §5, Prop 5.12 + Remark 5.13:
--
-- The path space between a and b is {a + b} ∩ κ⊥.
-- The operationalist axiom says ∪κ = V, so ∩κ⊥ = V⊥ = {0}.
-- Persistent equivalence (a + b ∈ ∩κ⊥) implies a + b = 0,
-- hence a = b.
--
-- The ua map (equivalence → identity) and idtoeqv (identity →
-- equivalence) are inverses.  Path space is contractible.

-- We state univalence as: if no discriminator separates a from b
-- across all κ-states, then a ≡ b.
-- This is exactly the operationalist axiom applied to the
-- discrimination system.

univalence : ∀ {A : Set} {Disc : Set} {a b : A}
  (separates : Disc → A → A → Set)
  → (∀ (d : Disc) → separates d a b → ⊥)
  → a ≡ b
univalence = operationalist

-- Paper: "Univalence is Galois-group exhaustion: the only
-- persistent orbit is the trivial orbit."
