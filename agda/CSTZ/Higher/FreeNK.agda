------------------------------------------------------------------------
-- CSTZ.Higher.FreeNK
--
-- Paper §7, Thm 7.15: Free (n,k)-structure.  [A]
--
-- S₃ symmetry provides directed structure at multiple levels.
-- The k-cells are the Grassmannian Gr(k,V) over GF(2): decomposable
-- k-forms, each determined by k independent 1-forms.
------------------------------------------------------------------------

module CSTZ.Higher.FreeNK where

open import CSTZ.GF2
open import CSTZ.Exterior.Basis

open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Paper §7, Thm 7.15

-- The number of directed levels k is determined by the subgroup
-- of S₃ employed.  For k > 3: iterate the triangle identity to
-- a tower of nested triangles.

-- k-morphisms are decomposable grade-k elements: products of k
-- independent grade-1 elements (discriminators).  These are exactly
-- the points of the Grassmannian Gr(k, GF(2)^n).

-- In our subset representation: a decomposable k-form is a subset
-- of size k where the k basis vectors are "independent" (i.e.,
-- the subset has exactly k true entries and corresponds to a
-- k-dimensional subspace).

-- Segal conditions: groupoids automatically satisfy Segal conditions
-- (unique fillers).  The Segal map from k-cells to composable
-- sequences of 1-cells is a bijection.
-- Full proof: Verification.Segal (App B.37).

-- Count of k-cells at dimension n: the Gaussian binomial [n choose k]_2
-- For GF(2), this counts the number of k-dimensional subspaces of GF(2)^n.
-- Examples:
--   Gr(1, GF(2)^3) = 7 points (the Fano plane)
--   Gr(2, GF(2)^3) = 7 lines (dual Fano)
--   Gr(1, GF(2)^2) = 3 points (the toroid)

-- The k-subsets of {0,...,n-1} in our Basis representation:
-- these are the decomposable k-forms (basis elements of Λ^k).
-- Non-decomposable elements of Λ^k are sums of basis elements;
-- they are chain-group elements, not k-morphisms.
