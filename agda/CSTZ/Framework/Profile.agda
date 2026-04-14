------------------------------------------------------------------------
-- CSTZ.Framework.Profile
--
-- Paper §3, Def 3.3: The membership profile of a datum a under
-- discriminator pair (d_τ, d_σ) is (τ_d(a), σ_d(a)) ∈ GF(2)².
------------------------------------------------------------------------

module CSTZ.Framework.Profile where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Framework.Discriminator

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

------------------------------------------------------------------------
-- Membership profile

-- Paper: "The membership profile of datum a under discriminator pair
-- (d_τ, d_σ) is (τ(a), σ(a)) ∈ GF(2)²."

Profile : Set
Profile = F × F

-- Compute the profile of element a under a discriminator pair
profile : (sys : DiscSystem) → DiscPair sys → DiscSystem.Pop sys → Profile
profile sys dp a = (DiscSystem.eval sys (d-τ dp) a , DiscSystem.eval sys (d-σ dp) a)
