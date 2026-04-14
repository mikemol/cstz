------------------------------------------------------------------------
-- CSTZ.Monoidal.Closure
--
-- Paper §8, Thm 8.13: Monoidal closure.  [Axiom class A]
--
-- "Hom(A ⊗ B, C) ≅ Hom(A, [B, C])"
-- The tensor-hom adjunction from the triangle identity.
-- Monoidal closure is not an additional property — it IS the
-- triangle identity applied at the morphism level.
------------------------------------------------------------------------

module CSTZ.Monoidal.Closure where

-- Paper §8, Thm 8.13:
-- The three components A⊗B, C, and [B,C] stand in the same
-- triadic relationship as κ, σ, τ: any two determine the third.
--
-- The bijection: given d witnessing A⊗B → C, d already has
-- τ_d(A)=1, τ_d(B)=1, σ_d(C)=1.  So d witnesses A → [B,C].
-- Conversely, given d' and e, their wedge product witnesses A⊗B → C.
--
-- Naturality in A: τ/σ assignments are functorial (preserved by
-- κ-deformations).
