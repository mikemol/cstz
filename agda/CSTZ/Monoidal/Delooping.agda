------------------------------------------------------------------------
-- CSTZ.Monoidal.Delooping
--
-- Paper §8, Thm 8.4: Delooping equivalence.  [A]
--
-- Rotating to σ-perspective performs delooping: a 2-category with
-- one object ≡ a monoidal 1-category.
------------------------------------------------------------------------

module CSTZ.Monoidal.Delooping where

open import CSTZ.GF2
open import CSTZ.Higher.Perspectives

------------------------------------------------------------------------
-- Paper §8, Thm 8.4

-- In the κ-perspective: population is S, discriminators are κ.
-- In the σ-perspective: population is κ (discriminators are now
-- things being discriminated), regime is σ.

-- Delooping identification:
-- - 1-morphisms of κ-perspective become OBJECTS of σ-perspective
-- - 2-morphisms of κ-perspective become 1-morphisms of σ-perspective
-- - The wedge product of two κ-discriminators (a 2-cell in κ) becomes
--   the monoidal product of two σ-objects

-- This IS Baez-Dolan delooping: an (n+1)-category with one object is
-- equivalently a monoidal n-category.  The single object corresponds
-- to the entire population S (collapsed to a point from the meta-level).

-- The rotation is performed by `rotate σ-persp` from Perspectives.agda.
-- The algebraic operation is identical; only the categorical
-- interpretation changes.

-- Proof: the identification is exact because the triangle identity
-- κ = σ + τ means the σ-rotation is lossless (invertible by rotating
-- back).  The monoidal product in the σ-perspective is literally
-- the wedge product of the κ-perspective's morphisms.
