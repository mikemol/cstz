------------------------------------------------------------------------
-- CSTZ.Category.Limits
--
-- Paper §6, Prop 6.20: Limits from exhaustive filtration.  [A]
--
-- Five limit types; universality from GF(2)-linearity.
-- Missing limits are residues that specify their own filling.
------------------------------------------------------------------------

module CSTZ.Category.Limits where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Category.Emergent

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §6, Prop 6.20

-- The five limit types constructible in C(S,κ):

data LimitKind : Set where
  terminal  : LimitKind   -- The trivial κ-equivalence class
  product   : LimitKind   -- Computed at κ₁ ∨ κ₂ (join of stages)
  equalizer : LimitKind   -- Kernel of difference morphism
  pullback  : LimitKind   -- Product + equalizer
  general   : LimitKind   -- Iterated pullback

-- Paper §6, Prop 6.20:
-- "A missing limit is a residue that specifies its own filling;
-- consuming it via κ-evolution gives the limit in the extended
-- category."

-- Terminal object: the single equivalence class that all
-- discriminators map to the same profile.  Under the zero
-- discriminator, everything collapses to one class.

-- Product A × B: exists at κ₁ ∨ κ₂ where κ₁ resolves A and
-- κ₂ resolves B.  The product object is the pair of equivalence
-- classes, resolved at the join.

-- Equalizer: given f,g: A → B (two discriminators d_f, d_g),
-- the equalizer is {a ∈ A | d_f(a) = d_g(a)}, i.e., the kernel
-- of (d_f + d_g): the elements where the two discriminators agree.

-- Universality: factoring morphisms are UNIQUE because linear
-- maps over GF(2) are determined by their values on a basis.
-- This is the structural reason limits exist and are universal.

-- Full exhaustive construction: Verification.LimitsExhaustive (B.26).

-- Equalizer as kernel of discriminator difference:
equalizerWitness : ∀ {n} → GF2Vec n → GF2Vec n → GF2Vec n
equalizerWitness d-f d-g = d-f +V d-g
-- The equalizer of f and g is the set where d_f + d_g evaluates to 0.
-- Over GF(2), d_f + d_g = 0 iff d_f = d_g (since x + x = 0).
-- So the equalizer is { a | (d_f + d_g)(a) = 0 } = ker(d_f + d_g).
