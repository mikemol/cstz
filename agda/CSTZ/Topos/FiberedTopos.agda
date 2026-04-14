------------------------------------------------------------------------
-- CSTZ.Topos.FiberedTopos
--
-- Paper §9, Thm 9.6: ∫C is an elementary topos.  [AP]
--
-- The Grothendieck construction ∫C over the poset of κ-states
-- forms an elementary topos.
------------------------------------------------------------------------

module CSTZ.Topos.FiberedTopos where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Topos.SubobjClassifier

open import Data.Nat using (ℕ ; _≤_)
open import Data.List using (List)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §9, Def 9.5: The fibered category

-- K = poset of κ-states under sub-regime inclusion.
-- For GF(2)^n, this is the poset of subspaces of (GF(2)^n)*,
-- which is a modular lattice (Verification.RISC, App B.38).

-- Objects of ∫C: (κ, A) — an equivalence class at resolution κ.
record FiberedObj (n : ℕ) : Set where
  field
    regime-dim : ℕ               -- dimension of κ
    dim-bound  : regime-dim ≤ n  -- κ is a sub-regime of V
    classRep   : GF2Vec n        -- representative of the equivalence class

-- Morphisms of ∫C: carry regime inclusions + morphisms in finer category.
record FiberedMor (n : ℕ) (src dst : FiberedObj n) : Set where
  field
    -- The target regime is at least as fine as the source
    regime-incl : FiberedObj.regime-dim src ≤ FiberedObj.regime-dim dst
    -- Plus a morphism in the finer category (a discriminator witness)
    witness     : GF2Vec n

------------------------------------------------------------------------
-- Paper §9, Thm 9.6: Elementary topos

-- ∫C is an elementary topos:
-- 1. Finite limits: computed at the finite join κ₁ ∨ κ₂.
--    No completed infinity needed.
-- 2. Subobject classifier: Ω = GF(2)², constant across fibers.
-- 3. Power objects: Ω^B = [B, Ω] exists by monoidal closure.
-- 4. K is a modular lattice: V* is a vector space, so its
--    subspace lattice is modular (strictly stronger than the
--    join-semilattice that O4 required).

-- The operationalist axiom is needed only for infinite-limit claims.
-- For any finite collection of κ-states, the join exists and all
-- topos operations are computable at the join.
