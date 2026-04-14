------------------------------------------------------------------------
-- CSTZ.Topos.ProofTheory
--
-- Paper §9, Thm 9.11: Dynamic proof theory.  [Axiom class A]
--
-- Static: within fixed κ, logic is Belnap FDE (four-valued).
-- Dynamic: κ-evolution resolves residues toward the Boolean middle.
------------------------------------------------------------------------

module CSTZ.Topos.ProofTheory where

open import CSTZ.GF2
open import CSTZ.Framework.FourCell using (ordered-τ ; ordered-σ ; gap ; over)
open import CSTZ.Topos.SubobjClassifier

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- Paper §9, Thm 9.11:
-- Conjunction = componentwise multiplication
-- Disjunction = componentwise maximum
-- Negation = swap: ¬(τ,σ) = (σ,τ)
-- Double negation elimination: ¬¬p = p  (swap twice = identity)
-- Excluded middle FAILS at the gap: (0,0) ∨ ¬(0,0) = (0,0)

-- Double negation elimination: proven
dne : ∀ (p : Ω) → ¬Ω (¬Ω p) ≡ p
dne (τ , σ) = refl

-- Excluded middle fails at the gap
em-fails-at-gap : gap ∨Ω ¬Ω gap ≡ gap
em-fails-at-gap = refl

-- Excluded middle holds at Boolean states
em-holds-at-τ : ordered-τ ∨Ω ¬Ω ordered-τ ≡ over
em-holds-at-τ = refl

em-holds-at-σ : ordered-σ ∨Ω ¬Ω ordered-σ ≡ over
em-holds-at-σ = refl

-- Paper: "Boolean structure is a local achievement.  The gap is
-- where Booleanness has not been earned."
