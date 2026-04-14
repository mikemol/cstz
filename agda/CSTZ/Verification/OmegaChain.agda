------------------------------------------------------------------------
-- CSTZ.Verification.OmegaChain
--
-- Paper App B.35: ω-chain stabilization.  [Axiom class AO]
--
-- The ascending chain of κ-states stabilizes because V is
-- finite-dimensional.  The limit regime is the finite span of
-- individual dᵢ's.  Profile linearity: linear combinations of
-- non-separating discriminators are non-separating.
------------------------------------------------------------------------

module CSTZ.Verification.OmegaChain where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Nat using (ℕ ; _≤_ ; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Stabilization argument (Paper B.35)

-- An ascending chain κ₁ ⊆ κ₂ ⊆ ⋯ of subspaces of V* (where
-- dim(V) = n) must stabilize in at most n steps, because each
-- strict inclusion increases dimension by ≥ 1.

-- After stabilization: the limit regime κ_∞ = ∪ κᵢ is a subspace
-- of V*, hence finite-dimensional (≤ n).

-- Profile linearity ensures: if d₁,...,dₖ all fail to separate
-- a from b (i.e., dᵢ·(a+b) = 0 for all i), then any linear
-- combination c₁d₁ + ⋯ + cₖdₖ also fails (by linearity of
-- the dot product).

-- Galois perspective: the residual symmetry group Gal(V/κ_∞)
-- contains exactly the "unbreakable symmetries" — those preserved
-- by every discriminator in the limit regime.

-- The operationalist axiom (O) then says: if no discriminator in
-- κ_∞ separates a from b, then a = b.
