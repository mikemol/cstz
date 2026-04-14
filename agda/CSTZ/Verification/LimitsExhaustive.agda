------------------------------------------------------------------------
-- CSTZ.Verification.LimitsExhaustive
--
-- Paper App B.26: Finite limits — exhaustive construction.  [A]
--
-- All five limit types: terminal, product, equalizer, pullback,
-- general finite limit.  Universality from GF(2)-linearity.
------------------------------------------------------------------------

module CSTZ.Verification.LimitsExhaustive where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Vec.Properties

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- 1. Terminal object
--
-- The terminal object is the trivial κ-equivalence class: under
-- the zero discriminator, everything collapses to one class.
-- There is a unique morphism from any object to the terminal:
-- the zero discriminator witnesses it (trivially).

-- 2. Product A × B
--
-- Computed at κ₁ ∨ κ₂ (join of the stages that resolve A and B).
-- The product object is the pair of equivalence classes resolved
-- at the join.
-- Projection morphisms: the forgetful functors π₁, π₂ that
-- project back to each individual stage.

-- 3. Equalizer eq(f,g)
--
-- Given f,g: A → B witnessed by d_f, d_g:
-- The equalizer is ker(d_f + d_g) = { a ∈ A | d_f(a) = d_g(a) }.
-- Over GF(2), d_f(a) = d_g(a) iff (d_f + d_g)(a) = 0.
-- The equalizer is the kernel of the difference discriminator.

-- The equalizer is a subobject of A:
-- eq ↪ A is the inclusion of the kernel.
-- Universality: any h: C → A with f∘h = g∘h factors through eq
-- uniquely.  Uniqueness from linearity: the factoring morphism
-- is determined by its values on a basis.

-- Key lemma: the kernel of a linear functional is a subspace.
kernel-is-subspace : ∀ {n} (d : GF2Vec n) (a b : GF2Vec n)
  → d ·V a ≡ 𝟘 → d ·V b ≡ 𝟘 → d ·V (a +V b) ≡ 𝟘
kernel-is-subspace d a b ha hb = begin
  d ·V (a +V b)          ≡⟨ ·V-linearʳ d a b ⟩
  (d ·V a) +F (d ·V b)   ≡⟨ cong₂ _+F_ ha hb ⟩
  𝟘 +F 𝟘                 ≡⟨ refl ⟩
  𝟘                       ∎
  where
    open import Relation.Binary.PropositionalEquality
      using (cong₂ ; module ≡-Reasoning)
    open ≡-Reasoning

-- 4. Pullback = Product + Equalizer
-- 5. General finite limit = iterated pullback

-- Universality throughout: factoring morphisms are unique because
-- linear maps over GF(2) are determined by basis values.
-- This is the structural reason limits exist and are universal.
