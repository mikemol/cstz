------------------------------------------------------------------------
-- CSTZ.Framework.Membership
--
-- Paper §3, Def 3.12: Membership as a ternary relation.
--
-- "a ∈_{(d_τ,d_σ),κ} S iff τ_d(a) = 1"
--
-- Membership depends on three things: element, collection, and
-- discriminator pair.  This is the key departure from ZFC, where
-- membership is binary.
------------------------------------------------------------------------

module CSTZ.Framework.Membership where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Framework.Discriminator
open import CSTZ.Framework.Profile

open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Ternary membership

-- Paper §3, Def 3.12: "a ∈_{dp,κ} S iff τ_{d_τ}(a) = 1"
-- The element a is a member of the collection (under discriminator
-- pair dp) when the τ-side discriminator fires on a.

Membership : (sys : DiscSystem) → DiscPair sys → DiscSystem.Pop sys → Set
Membership sys dp a = DiscSystem.eval sys (d-τ dp) a ≡ 𝟙
