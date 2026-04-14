------------------------------------------------------------------------
-- CSTZ.Framework.FourCell
--
-- Paper §3: The four-cell structure.
--
-- The membership profile (τ(a), σ(a)) ∈ GF(2)² takes four values:
--   (1,0) = ordered-τ    (discriminated to the τ side)
--   (0,1) = ordered-σ    (discriminated to the σ side)
--   (0,0) = gap          (neither predicate fires — novelty)
--   (1,1) = over      (both predicates fire — abstraction)
------------------------------------------------------------------------

module CSTZ.Framework.FourCell where

open import CSTZ.GF2
open import CSTZ.Framework.Profile

open import Data.Product using (_×_ ; _,_)

------------------------------------------------------------------------
-- Named cell constructors

ordered-τ : Profile
ordered-τ = (𝟙 , 𝟘)

ordered-σ : Profile
ordered-σ = (𝟘 , 𝟙)

gap : Profile
gap = (𝟘 , 𝟘)

over : Profile
over = (𝟙 , 𝟙)

------------------------------------------------------------------------
-- Cell classification

data CellKind : Set where
  is-ordered-τ : CellKind
  is-ordered-σ : CellKind
  is-gap       : CellKind
  is-over   : CellKind

classify : Profile → CellKind
classify (false , false) = is-gap
classify (true  , false) = is-ordered-τ
classify (false , true)  = is-ordered-σ
classify (true  , true)  = is-over

-- Paper §3: "Boolean states are (1,0) and (0,1); these have χ = 1.
-- Residue states are (0,0) and (1,1); these have χ = 0."
isBoolean : Profile → Bool
isBoolean (true  , false) = true
isBoolean (false , true)  = true
isBoolean _               = false

isResidue : Profile → Bool
isResidue p = not (isBoolean p)
