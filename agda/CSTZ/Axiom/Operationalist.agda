------------------------------------------------------------------------
-- CSTZ.Axiom.Operationalist
--
-- Axiom (O): The operationalist axiom.
--
-- Paper §1, Def 1.1: "If a distinction cannot be witnessed by any
-- discriminator in any κ-state, it is not a valid distinction."
--
-- Equivalently: if no κ-evolution produces a discriminator that
-- separates two claims, they are κ-equivalent and hence identical
-- by extensionality.
--
-- This is the framework's most philosophically contentious
-- commitment.  It powers infinity (Prop 4.26), infinite choice
-- (Thm 4.33ii), and univalence (Prop 5.12).
--
-- Axiom class: AO.  8 formal objects depend on this.
------------------------------------------------------------------------

module CSTZ.Axiom.Operationalist where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)

postulate
  operationalist :
    ∀ {A : Set} {Disc : Set} {a b : A}
      (separates : Disc → A → A → Set)
    → (∀ (d : Disc) → separates d a b → ⊥)
    → a ≡ b
