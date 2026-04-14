------------------------------------------------------------------------
-- CSTZ.Category.Directed
--
-- Paper §6, Def 6.1: Directed morphism.  [Axiom class A]
--
-- "f: a → b is a discriminator d with τ_d(a) = 1 and σ_d(b) = 1."
-- Direction comes from the τ/σ asymmetry.
------------------------------------------------------------------------

module CSTZ.Category.Directed where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Framework.Discriminator

open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Paper §6, Def 6.1: A directed morphism from a to b under
-- discrimination system sys is a discriminator d such that
-- τ_d(a) = 1 (source classified on τ side) and
-- σ_d(b) = 1 (target classified on σ side).

-- We represent this as a record bundling the discriminator
-- with its directedness witnesses.

record DirectedMorphism (sys : DiscSystem) (a b : DiscSystem.Pop sys) : Set where
  field
    witness   : DiscSystem.Disc sys
    τ-fires-a : DiscSystem.eval sys witness a ≡ 𝟙
    σ-fires-b : DiscSystem.eval sys witness b ≡ 𝟙
    -- Note: in the paper, σ_d(b) uses a SEPARATE σ-side evaluation.
    -- Here we use the same eval for simplicity; the τ/σ distinction
    -- is tracked in the Framework.Profile module.

-- Paper §6, Prop 6.2: Non-invertibility.
-- Reversing a → b requires a SEPARATE discriminator d' with
-- τ_{d'}(b) = 1 and σ_{d'}(a) = 1.  This costs one κ-dimension.
-- Invertibility costs two κ-dimensions total.
