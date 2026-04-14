------------------------------------------------------------------------
-- CSTZ.Examples.GF2Cubed.Cycles
--
-- Paper App E.2: ∈-induction with cycles (O2 resolution).
--
-- 2-cycle: a₃ ∈ a₅ ∈ a₃ (link vector e₁+e₂, 1 dimension)
-- 3-cycle: a₁ ∈ a₂ ∈ a₃ ∈ a₁ (link vectors sum to zero)
-- Chain+cycle composite structure.
------------------------------------------------------------------------

module CSTZ.Examples.GF2Cubed.Cycles where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Examples.GF2Cubed.Setup

open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- 2-cycle: a₃ ∈ a₅ ∈ a₃

-- Link vector: a₃ + a₅ = 011 + 101 = 110 = e₁ + e₂
cycle2-link : a₃ +V a₅ ≡ e₁+e₂
cycle2-link = refl

-- One link vector → 1 dimension consumed by the cycle.
-- This is consistent with foundation: no self-loop (a₃ ≠ a₅).

------------------------------------------------------------------------
-- 3-cycle: a₁ ∈ a₂ ∈ a₃ ∈ a₁

-- Link vectors:
-- v₁ = a₁ + a₂ = 001 + 010 = 011 = e₂ + e₃
cycle3-v₁ : a₁ +V a₂ ≡ e₂+e₃
cycle3-v₁ = refl

-- v₂ = a₂ + a₃ = 010 + 011 = 001 = e₃
cycle3-v₂ : a₂ +V a₃ ≡ e₃
cycle3-v₂ = refl

-- v₃ = a₃ + a₁ = 011 + 001 = 010 = e₂
cycle3-v₃ : a₃ +V a₁ ≡ e₂
cycle3-v₃ = refl

-- Sum of link vectors in a cycle = 0 (they close):
-- v₁ + v₂ + v₃ = (e₂+e₃) + e₃ + e₂ = 0
cycle3-closes : e₂+e₃ +V e₃ +V e₂ ≡ 𝟎
cycle3-closes = refl

-- 3 link vectors but only 2 independent (v₃ = v₁ + v₂).
-- So the cycle consumes at most 2 dimensions.
-- A k-cycle consumes at most k-1 independent link vectors.

------------------------------------------------------------------------
-- Chain + cycle composite: a₇ ∋ a₃ ∈ a₅ ∈ a₃

-- Chain link: a₇ + a₃ = e₁ (independent of cycle link e₁+e₂)
chain-link : a₇ +V a₃ ≡ e₁
chain-link = refl

-- Total depth: 1 (chain) + 1 (cycle) = 2 dimensions.
-- Independent: e₁ and e₁+e₂ are linearly independent.
chain-cycle-indep : e₁ +V e₁+e₂ ≡ e₂  -- their sum is e₂ ≠ 0
chain-cycle-indep = refl

------------------------------------------------------------------------
-- General: induction on dim(V/κ)
--
-- Each independent link vector reduces dim(V/κ) by 1.
-- Cycles consume ≤ k-1 dimensions (dependent link at closure).
-- So ∈-induction works modulo cycle equivalence:
-- induct on dim(V/κ), which strictly decreases along
-- independent links regardless of whether cycles exist.
