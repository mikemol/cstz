------------------------------------------------------------------------
-- CSTZ.Higher.Perspectives
--
-- Paper §7, Prop 7.11: Three perspectives.  [A]
-- Paper §7, Prop 7.12: Dynamics transfer under S₃ rotation.  [A]
--
-- κ-perspective: directed 1-morphisms (discriminators act on population)
-- σ-perspective: directed 2-morphisms (discriminating discriminators)
-- τ-perspective: third directed level
------------------------------------------------------------------------

module CSTZ.Higher.Perspectives where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Higher.Triangle

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

------------------------------------------------------------------------
-- Paper §7, Prop 7.11: Three perspectives

-- A perspective assigns one vertex of the toroid as the "regime"
-- and the other two as "masks" (τ and σ roles).

data Perspective : Set where
  κ-persp σ-persp τ-persp : Perspective

-- Each perspective rotation relabels the three toroid vertices.
-- Over GF(2)², the rotation is just permutation of the three
-- non-zero points {(1,0), (0,1), (1,1)}.

rotate : Perspective → (F × F) → (F × F)
rotate κ-persp p       = p                  -- identity
rotate σ-persp (τ , σ) = (σ , τ +F σ)      -- σ becomes regime
rotate τ-persp (τ , σ) = (τ +F σ , τ)      -- τ becomes regime

------------------------------------------------------------------------
-- Paper §7, Prop 7.12: Dynamics transfer

-- Monotonicity, write path linearity, and read path monoidal
-- properties transfer under S₃ rotation because they are
-- consequences of the GF(2) algebra, not of the label assignment.
--
-- The bilinear pairing ev(d,a) = ⟨d,a⟩ is GL-invariant.
-- S₃ ⊂ GL(2, GF(2)), so S₃ rotation preserves the pairing.
-- Profile linearity and evaluation linearity SWAP under rotation
-- (since rotating swaps the two arguments of the pairing);
-- since both hold, both are preserved.

-- The S₃ symmetry group has order 6.
-- GL(2, GF(2)) ≅ S₃ (order 6), so S₃ IS the full automorphism
-- group of the toroid.
