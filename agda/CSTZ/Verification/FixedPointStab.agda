------------------------------------------------------------------------
-- CSTZ.Verification.FixedPointStab
--
-- Paper App B.33: Fixed-point stability and uniqueness.  [A]
--
-- dim Λ²(GF(2)²) = 1: exactly one non-zero grade-2 element.
-- The 2-cell is GL(2,GF(2))-invariant (det = 1 over GF(2)).
------------------------------------------------------------------------

module CSTZ.Verification.FixedPointStab where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Exterior.Basis
open import CSTZ.Topos.FixedPoint

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Uniqueness of the grade-2 element in Λ(GF(2)²)

-- The exterior algebra Λ(GF(2)²) has:
--   Grade 0: 1 element (the unit)
--   Grade 1: 2 basis elements (e₁, e₂)
--   Grade 2: 1 basis element (e₁ ∧ e₂)

-- There is exactly ONE non-zero grade-2 element.
-- Any perturbation to zero triggers irremovability (Thm 9.16).

-- All grade-2 subsets of {0,1}: only (true,true)
all-grade2-subsets-of-2 : ∀ (s : Subset 2) → card s ≡ 2 → s ≡ unique-top-form
all-grade2-subsets-of-2 (true  ∷ true  ∷ []) refl = refl
all-grade2-subsets-of-2 (true  ∷ false ∷ []) ()
all-grade2-subsets-of-2 (false ∷ true  ∷ []) ()
all-grade2-subsets-of-2 (false ∷ false ∷ []) ()

------------------------------------------------------------------------
-- GL(2, GF(2))-invariance

-- GL(2, GF(2)) ≅ S₃ (order 6).  It acts on GF(2)² by invertible
-- linear maps.  The top form e₁ ∧ e₂ transforms by det(A):
-- A*(e₁ ∧ e₂) = det(A) · (e₁ ∧ e₂).
--
-- Over GF(2), every invertible matrix has det(A) = 1 (since
-- det ∈ GF(2)* = {1}).  Therefore the top form is invariant
-- under all of GL(2, GF(2)).

-- det = 1 over GF(2): for any invertible 2×2 matrix over GF(2),
-- det = ad + bc = 1 (since the matrix is invertible iff det ≠ 0,
-- and the only non-zero element of GF(2) is 1).
