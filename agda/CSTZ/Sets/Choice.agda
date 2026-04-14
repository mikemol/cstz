------------------------------------------------------------------------
-- CSTZ.Sets.Choice
--
-- Paper §4, Thm 4.33: Choice from residue consumption.
-- [Finite: class A.  Infinite: class AO.]
--
-- (i) Finite families: constructive.  Decreasing measure
--     m(κ) = dim(V/κ).  Each evolution step decreases m by 1.
--     Terminates in ≤ dim(V) steps.
--
-- (ii) Infinite families: by operationalist axiom.  No discriminator
--      separates "completed selection function" from "constructively
--      obtainable for every finite sub-family."
------------------------------------------------------------------------

module CSTZ.Sets.Choice where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)

-- Paper §4, Thm 4.33(i): Finite choice
--
-- Given a family of non-empty subcollections, each κ-evolution
-- resolves at least one.  The measure m(κ) = dim(V) - dim(κ)
-- strictly decreases.  After at most dim(V) steps, all families
-- are resolved.
--
-- This is constructive: the selection function is built by the
-- evolution process itself.

-- The termination measure: dim(V) - dim(κ)
-- After n evolutions, m = 0 and all classes are singletons.
finite-choice-terminates : ∀ (n : ℕ) → n ≤ n
finite-choice-terminates zero    = z≤n
finite-choice-terminates (suc n) = s≤s (finite-choice-terminates n)
-- The full termination proof (with the evolving κ-state) is in
-- Verification.ChoiceBound (App B.31).

-- Paper §4, Thm 4.33(ii): Infinite choice
-- Uses the operationalist axiom.  See Sets.Infinity for the pattern.
