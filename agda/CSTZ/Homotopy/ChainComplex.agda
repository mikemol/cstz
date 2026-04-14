------------------------------------------------------------------------
-- CSTZ.Homotopy.ChainComplex
--
-- Paper §5, Prop 5.5: ∂ ∘ ∂ = 0.  [Axiom class A]
--
-- "Each (k-2)-cell appears exactly twice in the double sum.
-- Over GF(2), 1+1=0, so every term cancels."
--
-- This is the defining property of a chain complex.  It connects
-- the algebraic residue concept to topological homological holes.
------------------------------------------------------------------------

module CSTZ.Homotopy.ChainComplex where

open import CSTZ.GF2
open import CSTZ.Exterior.Basis
open import CSTZ.Exterior.Boundary

open import Relation.Binary.PropositionalEquality using (_≡_)

-- Paper §5, Prop 5.5: The discrimination complex is a chain complex.
--
-- The proof is the postulated ∂∘∂≡0 from Exterior.Boundary.
-- We re-export it here under the paper's naming.

-- ∂ ∘ ∂ = 0: the boundary of a boundary is empty.
chain-complex : ∀ {n} (f : Exterior n) (t : Subset n) → ∂ (∂ f) t ≡ 𝟘
chain-complex = ∂∘∂≡0

-- Consequence: homology groups Hₖ = ker ∂ₖ / im ∂ₖ₊₁ are well-defined.
-- These classify the "holes" in the discrimination regime — the
-- residues that have not yet been consumed.
