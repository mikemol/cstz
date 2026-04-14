------------------------------------------------------------------------
-- CSTZ.Homotopy.Complex
--
-- Paper §5, Def 5.2: The discrimination complex.  [Axiom class A]
--
-- "The discrimination complex of a regime κ with dim(κ) = n is
-- Λ(GF(2)^n) = ⊕ₖ Λ^k(GF(2)^n), with grading:
--   Grade 0: degenerate (self-)discriminations
--   Grade k: k-fold non-degenerate compound discriminations"
------------------------------------------------------------------------

module CSTZ.Homotopy.Complex where

open import CSTZ.GF2
open import CSTZ.Exterior.Basis
open import CSTZ.Exterior.Graded

open import Data.Nat using (ℕ)

-- The discrimination complex is exactly the exterior algebra
-- Λ(GF(2)^n) with its graded structure.  The type `Exterior n`
-- from Exterior.Basis, together with `grade` and `restrictToGrade`
-- from Exterior.Graded, IS the discrimination complex.
--
-- No new definitions needed — this module documents the
-- identification and re-exports the relevant types.

-- The complex at dimension n
DiscComplex : ℕ → Set
DiscComplex = Exterior

-- Grade-k component: k-fold compound discriminations
gradeComponent : ∀ {n} → ℕ → DiscComplex n → DiscComplex n
gradeComponent = restrictToGrade
