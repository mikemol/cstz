------------------------------------------------------------------------
-- CSTZ.Verification.RISC
--
-- Paper App B.38: O1 and O4 — the RISC instruction set.  [A]
--
-- O1: Admissible discriminators are exactly V* (linear functionals).
-- O4: κ-states form a modular lattice (subspace lattice of V*).
-- Both are consequences of V* being a vector space over GF(2).
------------------------------------------------------------------------

module CSTZ.Verification.RISC where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Vec.Properties

open import Data.Nat using (ℕ ; _^_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- O1: Characterization of admissible discriminators

-- A function f: GF(2)^n → GF(2) is admissible (as a discriminator)
-- iff f(a+b) = f(a) + f(b).  These are exactly the GF(2)-linear
-- functionals: elements of V* = Hom(V, GF(2)).

-- Over GF(2), V* ≅ V (the dual is canonically isomorphic to V).
-- Every linear functional is the dot product with some vector.
-- So: admissible discriminators = vectors in GF(2)^n.

-- Count: |V*| = 2^n (including zero).  Non-trivial: 2^n - 1.
-- At n=3: 8 admissible (including zero), 7 non-trivial.
-- These 7 are the points of PG(2, GF(2)), the Fano plane.

admissible-count : ∀ (n : ℕ) → ℕ
admissible-count n = 2 ^ n

-- Non-trivial admissible discriminators
nontrivial-count : ∀ (n : ℕ) → ℕ
nontrivial-count n = 2 ^ n Data.Nat.∸ 1
  where open import Data.Nat using (_∸_)

-- At n=3: 7 non-trivial
nontrivial-at-3 : nontrivial-count 3 ≡ 7
nontrivial-at-3 = refl

-- The compression ratio: 2^n / 2^{2^n} = admissible / total Boolean functions
-- At n=3: 8/256 = 3.1%

total-boolean-at-3 : 2 ^ (2 ^ 3) ≡ 256
total-boolean-at-3 = refl

admissible-at-3 : 2 ^ 3 ≡ 8
admissible-at-3 = refl

------------------------------------------------------------------------
-- O4: κ-states form a modular lattice

-- κ-states are subspaces of V*.  V* is a vector space.
-- The lattice of subspaces of a finite-dimensional vector space
-- is a modular lattice.  This is stronger than join-semilattice.

-- Join: κ₁ ∨ κ₂ = span(κ₁ ∪ κ₂)
-- Meet: κ₁ ∧ κ₂ = κ₁ ∩ κ₂

-- Modularity: if κ₁ ⊆ κ₃, then κ₁ ∨ (κ₂ ∧ κ₃) = (κ₁ ∨ κ₂) ∧ κ₃
-- This is a standard result from linear algebra; we state it.

-- Profile linearity is preserved under joins: every element of
-- span(κ₁ ∪ κ₂) is a GF(2)-linear combination of linear functionals,
-- hence a linear functional.

-- Consequence: the fibered topos (Thm 9.6) has its required
-- join-semilattice property with room to spare.
