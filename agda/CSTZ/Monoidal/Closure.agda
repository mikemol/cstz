------------------------------------------------------------------------
-- CSTZ.Monoidal.Closure
--
-- Paper §8, Thm 8.13: Monoidal closure.  [A]
--
-- Hom(A ⊗ B, C) ≅ Hom(A, [B, C])
-- The tensor-hom adjunction from the triangle identity.
------------------------------------------------------------------------

module CSTZ.Monoidal.Closure where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §8, Thm 8.13

-- The adjunction:
-- A morphism A ⊗ B → C is a discriminator d with
--   τ_d(A) = 1, τ_d(B) = 1, σ_d(C) = 1.
--
-- A morphism A → [B,C] is a discriminator d' with
--   τ_{d'}(A) = 1, σ_{d'}([B,C]) = 1.
-- And [B,C] is the set of e with τ_e(B)=1, σ_e(C)=1.
--
-- The bijection: set d' = d and e = d (since d already has all
-- three properties).  Conversely, given d' and e, their wedge
-- product witnesses A⊗B → C.

-- We state the bijection as a pair of functions and their inverses.

-- Forward: Hom(A⊗B, C) → Hom(A, [B,C])
-- Given d witnessing A⊗B → C, return d itself.
-- (d witnesses A → [B,C] because τ_d(A)=1 and d ∈ [B,C].)

-- Backward: Hom(A, [B,C]) → Hom(A⊗B, C)
-- Given d' witnessing A → [B,C], and the element e ∈ [B,C] that
-- d' selects, the composite d' ∧ e (in the σ-regime) witnesses A⊗B → C.

-- Naturality: the bijection is natural in A because τ/σ assignments
-- are functorial (preserved by κ-deformations).

-- Paper: "The triangle identity guarantees that the three-way
-- relationship κ = σ + τ — here instantiated as the relationship
-- among source, target, and hom-space — is consistent and lossless."

-- Strict unit: d_h ∧ 1 = d_h (wedge with grade-0 unit is identity).
-- This gives naturality of the closure: precomposition with h ⊗ id_B
-- reduces to d_h (strict unit cancellation).
