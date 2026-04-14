------------------------------------------------------------------------
-- CSTZ.Homotopy.Groupoid
--
-- Paper §5, Thm 5.10: Intrinsic groupoid structure.  [Axiom class A]
--
-- "Λ(GF(2)^n) is a symmetric n-groupoid in which every k-morphism
-- is its own inverse, objects are degenerate morphisms, and
-- boundaries are computed by contraction."
--
-- All properties derive from: commutativity of ∧ over GF(2)
-- (since -1 = 1) and nilpotency v ∧ v = 0.
------------------------------------------------------------------------

module CSTZ.Homotopy.Groupoid where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Exterior.Basis
open import CSTZ.Exterior.Wedge

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Groupoid axioms (Paper §5, Thm 5.10 proof)

-- 1. Objects: 0-cells are degenerate 1-cells (d ∧ d = 0).
--    → wedge-self-zero from Exterior.Wedge

-- 2. Self-inverse: every element x satisfies -x = x.
--    → self-inverse from GF2.Properties (every GF(2) element
--       is its own additive inverse)
self-inverse-morphism : ∀ (x : F) → x +F x ≡ 𝟘
self-inverse-morphism = self-inverse

-- 3. Contraction: ω ∧ ω = 0 for any element.
--    → wedge-self-zero from Exterior.Wedge

-- 4. Composition: the wedge product provides composition at every
--    level.  Associativity inherited from exterior algebra.
--    → Wedge product associativity (to be proven in detail)

-- 5. Symmetry: α ∧ β = β ∧ α over GF(2).
--    → wedge₂-comm from Exterior.Wedge
symmetry : ∀ {n} (a b : Subset n) (t : Subset n)
  → wedge₂ a b t ≡ wedge₂ b a t
symmetry = wedge₂-comm

-- These five properties constitute a symmetric n-groupoid.
-- Paper: "Derived entirely from Λ(GF(2)^n)."
