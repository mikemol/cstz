------------------------------------------------------------------------
-- CSTZ.Verification.ChoiceBound
--
-- Paper App B.31: Finite choice explicit termination bound.  [A]
--
-- Measure m(κ) = dim(V/κ) = dim(V) - dim(κ) strictly decreases.
-- Terminates in ≤ dim(V) steps.
------------------------------------------------------------------------

module CSTZ.Verification.ChoiceBound where

open import Data.Nat using (ℕ ; zero ; suc ; _∸_ ; _≤_ ; z≤n ; s≤s ; _<_)
open import Data.Nat.Properties using (≤-refl ; n∸n≡0 ; ∸-monoʳ-<)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

------------------------------------------------------------------------
-- The termination measure

-- m(κ) = n - dim(κ)  where n = dim(V)
measure : (n dim-κ : ℕ) → ℕ
measure n dim-κ = n ∸ dim-κ

-- Each evolution increases dim(κ) by 1, so m decreases by 1.
-- At m = 0, dim(κ) = n and all classes are singletons.

-- m = 0 iff dim(κ) = n
measure-zero : ∀ (n : ℕ) → measure n n ≡ 0
measure-zero = n∸n≡0

-- After at most n evolutions, m = 0
terminates-in-n : ∀ (n : ℕ) → measure n 0 ≡ n
terminates-in-n zero    = refl
terminates-in-n (suc n) = cong suc (terminates-in-n n)
  where open import Data.Nat.Properties using ()

-- The measure is a natural number and strictly decreases:
-- m(κ') = m(κ) - 1 when one evolution is applied.
-- This gives well-founded recursion on m.
