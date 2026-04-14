------------------------------------------------------------------------
-- CSTZ.Category.Emergent
--
-- Paper §6, Def 6.5: The emergent category C(S,κ).  [Axiom class A]
--
-- Objects = κ-equivalence classes.
-- Morphisms = directed discriminators.
-- Identity = degenerate self-discrimination (d ∧ d = 0).
-- Composition = joint filtration (produces 2-cells, not 1-cells).
------------------------------------------------------------------------

module CSTZ.Category.Emergent where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Framework.Discriminator

-- Paper §6, Def 6.5:
-- C(S,κ) has:
--   Objects: κ-equivalence classes of elements of S
--   Morphisms: directed discriminators (Def 6.1)
--   Identity: the degenerate morphism d ∧ d = 0
--   Composition: via joint filtration (Def 6.6)
--
-- Paper §6, Def 6.6:
-- "g ∘ f = d₁ ∧ d₂ ∈ Λ²V"
-- Composition of two 1-morphisms produces a 2-cell.
-- The framework is 2-categorical from the start.

-- The category structure is parameterized by a DiscSystem and
-- a regime.  We define it as a module-level concept; the full
-- categorical axioms are verified in TwoCategory.agda.
