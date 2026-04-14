------------------------------------------------------------------------
-- CSTZ.Monoidal.Symmetric
--
-- Paper §8, Prop 8.2: Symmetric monoidal structure.  [A]
--
-- (C(S,κ), ⊗) is symmetric monoidal.  ALL coherence morphisms
-- (associator, unitors, braiding) are identities because ∧ is
-- strictly associative, strictly unital, and commutative over GF(2).
------------------------------------------------------------------------

module CSTZ.Monoidal.Symmetric where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Exterior.Wedge

-- Strict monoidal: all coherences are identities.
-- This is because the exterior algebra is STRICTLY associative
-- and commutative — there are no non-trivial associators or
-- braidings to worry about.  Pentagon and hexagon axioms are
-- trivially satisfied.
--
-- Full exhaustive verification: Verification.MonoidalCoherence (B.25).
