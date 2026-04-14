------------------------------------------------------------------------
-- CSTZ.Verification.Segal
--
-- Paper App B.37: Segal conditions at k ≥ 3.  [Axiom class A]
--
-- Groupoids automatically satisfy Segal conditions (unique fillers).
-- k-cells are the Grassmannian Gr(k,V) over GF(2): decomposable
-- k-forms, each determined by k independent 1-forms.
-- Non-decomposable elements are chain-group elements, not k-morphisms.
------------------------------------------------------------------------

module CSTZ.Verification.Segal where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Exterior.Basis
open import CSTZ.Exterior.Wedge

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Fact 1: Grade ≥ 2 elements are self-inverse.
-- ω ∧ ω = 0 for any element (wedge-self-zero from Exterior.Wedge).
-- Commutativity of ∧ means every k-morphism equals its reversal.

-- Fact 2: Groupoids satisfy Segal conditions.
-- Existence: given k composable, pairwise independent 1-forms
-- d₁,...,dₖ, their wedge d₁ ∧ ⋯ ∧ dₖ is non-zero.
-- Uniqueness: GF(2)* = {1}, so the determinant is trivial; any
-- basis for the same k-subspace yields the same wedge product.

-- The Segal map: Gr(k,V) → {k-tuples of independent 1-forms}/∼
-- is a bijection.

-- Explicit at k=3: d₁∧d₂∧d₃ is determined by {d₁,d₂,d₃} (unordered).
-- Its three 2-faces are d₁∧d₂, d₂∧d₃, d₁∧d₃.
-- Given the three 2-faces, the 3-cell is their unique filler.

-- Concrete verification: at n=3, the unique grade-3 basis element is
-- {0,1,2} = (true, true, true).  Its three grade-2 faces are
-- {0,1}, {1,2}, {0,2}.

top-3-cell : Subset 3
top-3-cell = true ∷ true ∷ true ∷ []

face-01 : Subset 3
face-01 = true ∷ true ∷ false ∷ []

face-12 : Subset 3
face-12 = false ∷ true ∷ true ∷ []

face-02 : Subset 3
face-02 = true ∷ false ∷ true ∷ []

-- Verify: these three 2-faces have grade 2
face-01-grade : card face-01 ≡ 2
face-01-grade = refl

face-12-grade : card face-12 ≡ 2
face-12-grade = refl

face-02-grade : card face-02 ≡ 2
face-02-grade = refl

-- The top cell has grade 3
top-3-cell-grade : card top-3-cell ≡ 3
top-3-cell-grade = refl

------------------------------------------------------------------------
-- Gaussian binomial coefficients (k-subspaces of GF(2)^n)
--
-- [n choose k]_2 = number of k-dimensional subspaces of GF(2)^n
-- [3 choose 1]_2 = 7  (points of Fano plane)
-- [3 choose 2]_2 = 7  (lines of Fano plane = dual)
-- [3 choose 3]_2 = 1  (the full space)

-- These are the number of decomposable k-forms = number of k-morphisms.
-- Non-decomposable elements (sums of basis elements) are chain-group
-- elements, not individual morphisms.
