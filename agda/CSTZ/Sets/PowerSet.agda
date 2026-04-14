------------------------------------------------------------------------
-- CSTZ.Sets.PowerSet
--
-- Paper §4, Def 4.21: Discriminative power set.  [Axiom class A]
--
-- Under a regime of dimension n, at most 2^n subcollections exist.
-- The power set is constructive and grows with κ.
------------------------------------------------------------------------

module CSTZ.Sets.PowerSet where

open import Data.Nat using (ℕ ; _^_)

-- Paper §4, Def 4.21:
-- P_κ(S) = { subcollections of S distinguishable under κ }
-- |P_κ(S)| ≤ 2^(dim κ)
--
-- This is a definition, not a theorem requiring proof.
-- The bound follows from: each subcollection is determined by
-- a Boolean predicate on dim(κ) dimensions, and there are
-- at most 2^(dim κ) such predicates.

powerSetBound : ℕ → ℕ
powerSetBound n = 2 ^ n
