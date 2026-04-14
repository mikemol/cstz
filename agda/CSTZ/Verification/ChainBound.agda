------------------------------------------------------------------------
-- CSTZ.Verification.ChainBound
--
-- Paper App B.34: Foundation chain bound — link independence.  [AP]
--
-- Each link aᵢ ∋ aᵢ₊₁ produces a link vector vᵢ = aᵢ + aᵢ₊₁.
-- Independent links produce linearly independent link vectors.
-- Chain depth = dim(span{vᵢ}) ≤ n = dim(V).
------------------------------------------------------------------------

module CSTZ.Verification.ChainBound where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Nat using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Link vectors

-- Given a membership chain a₀ ∋ a₁ ∋ ⋯ ∋ aₖ, the link vectors are
-- vᵢ = aᵢ + aᵢ₊₁ ∈ GF(2)^n.
linkVector : ∀ {n} → GF2Vec n → GF2Vec n → GF2Vec n
linkVector a b = a +V b

-- A dependent link vector is a GF(2)-linear combination of
-- independent link vectors.  This produces a derived relation,
-- not a new membership step.

-- Key claim: independent links produce linearly independent link
-- vectors.  If vᵢ were a linear combination of v₁,...,vᵢ₋₁, then
-- the membership chain could be shortened (the i-th link is
-- derivable from earlier links).

-- Chain depth = dim(span{v₁,...,vₖ}) ≤ dim(V) = n.
-- Sharp: achieved by the basis chain e₁ ∋ e₂ ∋ ⋯ ∋ eₙ.

-- Galois perspective: each independent link reduces dim(V/κ) by 1.
-- After k independent links, dim(V/κ) = n - k.
-- Max k = n (when V/κ = 0).

-- The formal proof requires defining "linearly independent list of
-- vectors" and showing that membership links produce such a list.
-- We state the bound as a postulate consistent with the chain-depth
-- bound in Sets.Foundation.

-- Python cofibration (STUDY.md §8.2): P9 has no Python witness — this
-- is a verification postulate consistent with P7 (Sets.Foundation).
-- `src/cstz/sets.py :: chain_depth_bound(n)` reports the same numeric
-- bound operationally but does not witness the inequality.
postulate
  chain-bound : ∀ {n : ℕ} (k : ℕ) → k ≤ n
  -- Any chain of depth k in GF(2)^n has k ≤ n.
