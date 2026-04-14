------------------------------------------------------------------------
-- CSTZ.Homotopy.Degeneracy
--
-- Paper §5, Def 5.1: Degeneracy as identity.  [Axiom class A]
--
-- "A 0-cell is a degenerate 1-cell: d ∧ d = 0.  There is only
-- discrimination.  Grade 0 is what results when a discrimination
-- collapses."
------------------------------------------------------------------------

module CSTZ.Homotopy.Degeneracy where

open import CSTZ.GF2
open import CSTZ.Exterior.Basis
open import CSTZ.Exterior.Wedge

-- Paper §5, Def 5.1:
-- "The object associated with discriminator d is the degenerate
-- self-discrimination of d.  Grade 0 is not 'scalars interpreted
-- as objects.'  Grade 0 is what results when a discrimination
-- collapses."
--
-- In our formalization: the wedge-self-zero theorem from
-- Exterior.Wedge already captures this: for any non-empty subset s,
-- wedge₂ s s = 𝟎E (the zero element).
--
-- This means: composing a discrimination with itself annihilates it.
-- The surviving grade-0 part is the identity / degenerate element.

-- Re-export the key property
open CSTZ.Exterior.Wedge public using (wedge-self-zero)
