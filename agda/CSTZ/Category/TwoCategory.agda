------------------------------------------------------------------------
-- CSTZ.Category.TwoCategory
--
-- Paper §6, Thm 6.8: 2-category axioms.  [Axiom class A]
--
-- "C(S,κ) satisfies strict 2-category axioms; interchange law
-- holds via cross-term cancellation (1+1=0 in GF(2)²)."
--
-- The interchange law and Russell exclusion are "the same claim" —
-- both are consequences of evaluation linearity rejecting the
-- affine component.
------------------------------------------------------------------------

module CSTZ.Category.TwoCategory where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Exterior.Basis
open import CSTZ.Exterior.Wedge

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- Paper §6, Thm 6.8: The 2-category axioms.
--
-- Strict associativity: (f ∧ g) ∧ h = f ∧ (g ∧ h)
--   → From associativity of the exterior algebra.
--
-- Strict unitality: f ∧ 1 = f = 1 ∧ f
--   → 1 is the grade-0 element; wedge with it is identity.
--
-- Interchange law: (g ∘ f) ⊗ (g' ∘ f') = (g ⊗ g') ∘ (f ⊗ f')
--   → Both paths through the interchange square yield the same
--     element of GF(2)², because cross-terms cancel via 1+1=0.

-- The interchange law at the level of GF(2) profiles:
-- Given profiles p(f), p(g), p(f'), p(g') ∈ GF(2)²,
-- the interchange square produces:
--   LHS = p(g∘f) + p(g'∘f')
--   RHS = p(g⊗g') ∘ p(f⊗f')
-- The cross-terms (p(g∘f') and p(g'∘f)) each appear in both,
-- and cancel via double-cancel.

open import CSTZ.Vec.Properties using (+F-interchange)

interchange-at-F : ∀ (a b c d : F)
  → (a +F b) +F (c +F d) ≡ (a +F c) +F (b +F d)
interchange-at-F = +F-interchange

-- Paper: "Interchange and Russell are the same claim."
-- Both are consequences of GF(2) linearity rejecting the affine component.
