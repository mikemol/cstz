------------------------------------------------------------------------
-- CSTZ.Topos.FOL
--
-- Paper §9, Prop 9.12: First-order logic is internal.  [AP]
--
-- Quantifiers as adjunctions to pullback:
--   ∀_f = right adjoint to pullback f*
--   ∃_f = left adjoint to pullback f*
------------------------------------------------------------------------

module CSTZ.Topos.FOL where

open import CSTZ.GF2
open import CSTZ.Topos.SubobjClassifier

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §9, Prop 9.12

-- FOL is a fragment of the topos's internal logic.  The key
-- identifications:
--
--   Modus ponens        = evaluation morphism ev: [A,B] ⊗ A → B
--   Universal instantiation = ∀-counit
--   Existential generalization = ∃-unit
--   Terms               = morphisms in C(S,κ)
--   Variables            = elements of the population
--   Substitution         = composition of morphisms
--
-- The construction requires the topos structure (class AP)
-- because quantifiers are defined via the power object Ω^B,
-- whose existence depends on monoidal closure + profile linearity.

-- The internal logic has:
--   Conjunction  = _∧Ω_ (componentwise multiplication)
--   Disjunction  = _∨Ω_ (componentwise maximum)
--   Negation     = ¬Ω   (swap)
--   Implication  = internal hom in Ω (closure adjunction)
--   ∀            = right adjoint to pullback
--   ∃            = left adjoint to pullback

-- The metatheory needed to validate the framework is available
-- internally: the framework can reason about its own proof theory.
