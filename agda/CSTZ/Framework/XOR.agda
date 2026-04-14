------------------------------------------------------------------------
-- CSTZ.Framework.XOR
--
-- Paper §3, Def 3.6-3.9: XOR signature and residue.
--
-- χ(a) = τ(a) + σ(a)   (the XOR signature)
-- χ = 1 means the datum is discriminated (Boolean)
-- χ = 0 means the datum is a residue (gap or overlap)
--
-- R(S) = { a ∈ S | χ(a) = 0 }  (the residue set)
------------------------------------------------------------------------

module CSTZ.Framework.XOR where

open import CSTZ.GF2
open import CSTZ.Framework.Profile
open import CSTZ.Framework.Discriminator

open import Data.Product using (proj₁ ; proj₂)

------------------------------------------------------------------------
-- XOR signature

-- Paper §3, Def 3.6: "χ(a) = τ(a) + σ(a)"
χ : Profile → F
χ p = proj₁ p +F proj₂ p

-- Paper: "χ = 1 means discriminated; χ = 0 means residue"
isDiscriminated : Profile → Bool
isDiscriminated p = χ p

------------------------------------------------------------------------
-- Residue predicate

-- Paper §3, Def 3.9: "R(S) = { a ∈ S | χ(a) = 0 }"
-- An element is a residue iff its XOR signature vanishes.
isResidueχ : Profile → Bool
isResidueχ p with χ p
... | false = true    -- χ = 0 → residue
... | true  = false   -- χ = 1 → discriminated
