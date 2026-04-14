------------------------------------------------------------------------
-- CSTZ.Higher.Toroid
--
-- Paper §7, Def 7.13: The GF(2) toroid.  [Axiom class A]
--
-- "The three non-zero points of GF(2)², forming a triangle with
-- S₃ as symmetry group.  Geometric manipulation of the toroid =
-- changes of categorical perspective."
------------------------------------------------------------------------

module CSTZ.Higher.Toroid where

open import CSTZ.GF2
open import CSTZ.Higher.Triangle

open import Data.Product using (_×_ ; _,_)

-- The GF(2) toroid = the three non-zero points of GF(2)²:
--   (1,0)  = τ-point
--   (0,1)  = σ-point
--   (1,1)  = κ-point
--
-- Each pair sums to the third (the triangle identity).
-- S₃ acts by permutation of the three points.
-- The zero point (0,0) is the center / degenerate element.

-- The toroid has exactly 3 non-zero points.
-- Its automorphism group is S₃ ≅ GL(2, GF(2)), order 6.
