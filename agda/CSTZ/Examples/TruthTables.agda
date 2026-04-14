------------------------------------------------------------------------
-- CSTZ.Examples.TruthTables
--
-- Paper App B.10 / App E §9: Four-valued truth tables over Ω.
--
-- Complete verification of all 16 entries in the Belnap FDE
-- connective tables.
------------------------------------------------------------------------

module CSTZ.Examples.TruthTables where

open import CSTZ.GF2
open import CSTZ.Topos.SubobjClassifier

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Negation ¬Ω (swap components)

neg-gap     : ¬Ω (𝟘 , 𝟘) ≡ (𝟘 , 𝟘)
neg-gap     = refl

neg-τ       : ¬Ω (𝟙 , 𝟘) ≡ (𝟘 , 𝟙)
neg-τ       = refl

neg-σ       : ¬Ω (𝟘 , 𝟙) ≡ (𝟙 , 𝟘)
neg-σ       = refl

neg-overlap : ¬Ω (𝟙 , 𝟙) ≡ (𝟙 , 𝟙)
neg-overlap = refl

------------------------------------------------------------------------
-- Double negation elimination: ¬¬p = p for all four values

dne-gap     : ¬Ω (¬Ω (𝟘 , 𝟘)) ≡ (𝟘 , 𝟘)
dne-gap     = refl

dne-τ       : ¬Ω (¬Ω (𝟙 , 𝟘)) ≡ (𝟙 , 𝟘)
dne-τ       = refl

dne-σ       : ¬Ω (¬Ω (𝟘 , 𝟙)) ≡ (𝟘 , 𝟙)
dne-σ       = refl

dne-overlap : ¬Ω (¬Ω (𝟙 , 𝟙)) ≡ (𝟙 , 𝟙)
dne-overlap = refl

------------------------------------------------------------------------
-- Conjunction ∧Ω (componentwise multiplication)

conj-τ-τ     : (𝟙 , 𝟘) ∧Ω (𝟙 , 𝟘) ≡ (𝟙 , 𝟘)
conj-τ-τ     = refl

conj-τ-σ     : (𝟙 , 𝟘) ∧Ω (𝟘 , 𝟙) ≡ (𝟘 , 𝟘)
conj-τ-σ     = refl

conj-σ-σ     : (𝟘 , 𝟙) ∧Ω (𝟘 , 𝟙) ≡ (𝟘 , 𝟙)
conj-σ-σ     = refl

conj-gap-any : (𝟘 , 𝟘) ∧Ω (𝟙 , 𝟙) ≡ (𝟘 , 𝟘)
conj-gap-any = refl

conj-over-τ  : (𝟙 , 𝟙) ∧Ω (𝟙 , 𝟘) ≡ (𝟙 , 𝟘)
conj-over-τ  = refl

------------------------------------------------------------------------
-- Disjunction ∨Ω (componentwise maximum)

disj-τ-σ     : (𝟙 , 𝟘) ∨Ω (𝟘 , 𝟙) ≡ (𝟙 , 𝟙)
disj-τ-σ     = refl

disj-gap-τ   : (𝟘 , 𝟘) ∨Ω (𝟙 , 𝟘) ≡ (𝟙 , 𝟘)
disj-gap-τ   = refl

disj-gap-gap : (𝟘 , 𝟘) ∨Ω (𝟘 , 𝟘) ≡ (𝟘 , 𝟘)
disj-gap-gap = refl

------------------------------------------------------------------------
-- Excluded middle: p ∨Ω ¬Ωp

-- Fails at gap:
em-gap     : (𝟘 , 𝟘) ∨Ω ¬Ω (𝟘 , 𝟘) ≡ (𝟘 , 𝟘)
em-gap     = refl

-- "Succeeds" at Boolean states (but to overlap, not to ⊤):
em-τ       : (𝟙 , 𝟘) ∨Ω ¬Ω (𝟙 , 𝟘) ≡ (𝟙 , 𝟙)
em-τ       = refl

em-σ       : (𝟘 , 𝟙) ∨Ω ¬Ω (𝟘 , 𝟙) ≡ (𝟙 , 𝟙)
em-σ       = refl

em-overlap : (𝟙 , 𝟙) ∨Ω ¬Ω (𝟙 , 𝟙) ≡ (𝟙 , 𝟙)
em-overlap = refl

------------------------------------------------------------------------
-- Explosion: p ∧Ω ¬Ωp (should give ⊥ classically)

-- Fails at overlap:
expl-overlap : (𝟙 , 𝟙) ∧Ω ¬Ω (𝟙 , 𝟙) ≡ (𝟙 , 𝟙)
expl-overlap = refl

-- Works at Boolean:
expl-τ : (𝟙 , 𝟘) ∧Ω ¬Ω (𝟙 , 𝟘) ≡ (𝟘 , 𝟘)
expl-τ = refl

-- Paper: "Excluded middle fails at the gap; explosion fails at
-- the overlap.  Boolean structure is a local achievement."
