------------------------------------------------------------------------
-- CSTZ.Topos.FixedPoint
--
-- Paper §9, Thm 9.15: Discrimination is a fixed point.  [A]
--
-- "dim Λ²(GF(2)²) = 1: exactly one non-zero grade-2 element
-- exists (e₁ ∧ e₂).  No alternative to perturb to."
------------------------------------------------------------------------

module CSTZ.Topos.FixedPoint where

open import CSTZ.GF2
open import CSTZ.Exterior.Basis

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- The unique grade-2 basis element of Λ(GF(2)²)
-- is the subset {0,1} = (true, true)
unique-top-form : Subset 2
unique-top-form = true ∷ true ∷ []

-- It has grade 2
unique-top-form-grade : card unique-top-form ≡ 2
unique-top-form-grade = refl

-- There is exactly ONE such element (2 choose 2 = 1).
-- No alternative to perturb to.  Perturbation to zero triggers
-- irremovability (reinstatement).
