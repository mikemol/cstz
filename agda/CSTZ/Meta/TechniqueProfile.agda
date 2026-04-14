------------------------------------------------------------------------
-- CSTZ.Meta.TechniqueProfile
--
-- Paper App D: Technique profile annotations (metadata).
--
-- The paper identifies 6 closure techniques used across 47 audited
-- claims.  Each claim has a binary profile in GF(2)⁶.  This module
-- defines the profile type and annotates key theorems.
--
-- Not proofs — just metadata for traceability and rotation analysis.
------------------------------------------------------------------------

module CSTZ.Meta.TechniqueProfile where

open import CSTZ.GF2
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- The 6 closure techniques (Paper App D, §D.1)

-- T1: Characteristic 2 (1+1=0)
-- T2: Graded Leibniz rule ∂(a∧b) = ∂a∧b + a∧∂b
-- T3: GF(2)-linearity
-- T4: Strict associativity/commutativity of ∧
-- T5: Short exact sequence and tensor decomposition
-- T6: Galois group structure

-- A technique profile is a vector in GF(2)⁶.
TechProfile : Set
TechProfile = Vec F 6

------------------------------------------------------------------------
-- Named technique flags

-- Convenience: technique profile with named positions.
-- Position 0=T1, 1=T2, 2=T3, 3=T4, 4=T5, 5=T6.

-- Example profiles from App D:

-- Russell exclusion: [T1, T3] = char2 + linearity
russell-profile : TechProfile
russell-profile = true ∷ false ∷ true ∷ false ∷ false ∷ false ∷ []

-- Interchange law: [T1, T3] = same as Russell (Claim F)
interchange-profile : TechProfile
interchange-profile = true ∷ false ∷ true ∷ false ∷ false ∷ false ∷ []

-- Paper App D, Claim F: "Russell exclusion and interchange are
-- the same claim — both are linearity over GF(2) rejecting the
-- affine/quadratic component."
claim-F : russell-profile ≡ interchange-profile
claim-F = refl

-- Chain complex ∂∘∂=0: [T1, T2] = char2 + Leibniz
chain-complex-profile : TechProfile
chain-complex-profile = true ∷ true ∷ false ∷ false ∷ false ∷ false ∷ []

-- Exhaustivity filling: [T2, T5] = Leibniz + SES
exhaustivity-profile : TechProfile
exhaustivity-profile = false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ []

-- Groupoid symmetry: [T1, T4] = char2 + strict ∧
groupoid-profile : TechProfile
groupoid-profile = true ∷ false ∷ false ∷ true ∷ false ∷ false ∷ []

-- Monoidal closure: [T4, T6] = strict ∧ + Galois
closure-profile : TechProfile
closure-profile = false ∷ false ∷ false ∷ true ∷ false ∷ true ∷ []

-- Foundation chain bound: [T3, T6] = linearity + Galois
foundation-profile : TechProfile
foundation-profile = false ∷ false ∷ true ∷ false ∷ false ∷ true ∷ []

------------------------------------------------------------------------
-- The rotation principle (Paper App D, §D.3-D.4)
--
-- Every proof can be rotated through the Galois hub (T6) to produce
-- an alternate proof from a different arm of the technique tree:
--   Algebraic arm: T1–T2–T5–T6
--   Coherence arm: T6–T4
--   Constraint arm: T6–T3
--
-- Exception: T2 (Leibniz) is the unique non-rotatable technique.
-- It IS the crossing operation (∂ across the tensor boundary),
-- not a property of the regime.

------------------------------------------------------------------------
-- Technique co-occurrence tree (Paper App D, §D.2)
--
-- T3 and T4 never co-occur in gap closures.
-- T6 (Galois) is the hub: pre-verified 19%, gap-closed 78%.
-- 18 distinct profiles span rank 6 in GF(2)⁶.
-- ~15-18 independent facts modulo rotation.
