------------------------------------------------------------------------
-- CSTZ.Sets.SymDiff
--
-- Paper §4, Prop 4.19: Symmetric difference as primitive.
-- [Axiom class A]
--
-- Over GF(2), τ_{d_A} + τ_{d_B} gives the symmetric difference
-- A △ B, not the union A ∪ B.  Union is derived.
------------------------------------------------------------------------

module CSTZ.Sets.SymDiff where

open import CSTZ.GF2

-- Symmetric difference of membership predicates over GF(2):
-- (τ_A + τ_B)(a) = τ_A(a) xor τ_B(a)
--
-- This gives: a ∈ A △ B iff a is in exactly one of A, B.
-- Union requires intersection: A ∪ B = (A △ B) △ (A ∩ B).
-- Over GF(2), symmetric difference is the primitive set operation.
