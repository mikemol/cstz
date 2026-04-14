------------------------------------------------------------------------
-- CSTZ.Exterior.Graded
--
-- The graded structure of the exterior algebra Λ(GF(2)^n).
--
-- Paper §2, §5: The exterior algebra is graded by k from 0 to n.
-- Grade 0 has dimension 1 (the scalars).  Grade k has dimension
-- (n choose k).  The total dimension is 2^n.
--
-- Grade 0 = degenerate self-discriminations (d ∧ d = 0).
-- Grade 1 = individual discriminators.
-- Grade k = k-fold non-degenerate compound discriminations.
------------------------------------------------------------------------

module CSTZ.Exterior.Graded where

open import CSTZ.GF2
open import CSTZ.Exterior.Basis

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_)

------------------------------------------------------------------------
-- Grade of a subset (number of true entries)

grade : ∀ {n} → Subset n → ℕ
grade = card

------------------------------------------------------------------------
-- Grade-restricted elements

-- An element of Λ^k(GF(2)^n): an Exterior element that is zero
-- outside grade k.
--
-- We don't enforce this in the type (which would require dependent
-- types on subset cardinality).  Instead, we provide a projection
-- that zeroes out non-grade-k contributions.

open import Relation.Nullary using (yes ; no)
open import Data.Nat.Properties using (_≟_)

restrictToGrade : ∀ {n} → ℕ → Exterior n → Exterior n
restrictToGrade k f s with card s ≟ k
... | yes _ = f s
... | no  _ = 𝟘

------------------------------------------------------------------------
-- Grade-0 element: the scalar part

-- A grade-0 element is determined by its value on the empty subset.
-- Over GF(2), grade 0 is 1-dimensional: {0, 1}.

scalar : ∀ {n} → F → Exterior n
scalar c s with card s
... | zero = c
... | _    = 𝟘

-- The unit of the exterior algebra (the grade-0 element 1)
unitE : ∀ {n} → Exterior n
unitE = scalar 𝟙
