------------------------------------------------------------------------
-- CSTZ.Topos.SelfEnrichment
--
-- Paper §9, Thm 9.2: Canonical self-enrichment.  [A]
--
-- Three enrichment ingredients = three vertices of the GF(2) toroid:
--   Hom-objects from σ-perspective
--   Composition from τ-perspective
--   Objects from κ-perspective
------------------------------------------------------------------------

module CSTZ.Topos.SelfEnrichment where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Higher.Triangle

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §9, Def 9.1: Enrichment data

-- An enrichment of C over (V, ⊗, I) requires:
record EnrichmentData (n : ℕ) : Set₁ where
  field
    HomObj    : Set                           -- hom-objects ∈ V
    compose   : HomObj → HomObj → HomObj      -- [B,C] ⊗ [A,B] → [A,C]
    identity  : HomObj                        -- I → [A,A]
    assoc     : ∀ h g f → compose (compose h g) f ≡ compose h (compose g f)
    unitˡ     : ∀ f → compose identity f ≡ f
    unitʳ     : ∀ f → compose f identity ≡ f

-- Paper §9, Thm 9.2:
-- C(S,κ) is canonically enriched over itself:
-- - HomObj = internal hom [A,B] = discriminators witnessing A → B
--   (from the σ-perspective: discriminators-as-data)
-- - compose = sequential filtration (wedge product of witnesses)
--   (from the τ-perspective: applying discriminators in sequence)
-- - identity = degenerate discriminator (grade-0 element)
--   (from the κ-perspective: the regime's own unit)
--
-- All coherences follow from the exterior algebra's strict
-- associativity, commutativity, and unitality.
-- The three enrichment ingredients map to the three toroid vertices:
-- no choices required — the enrichment is canonical.
