------------------------------------------------------------------------
-- CSTZ.Framework.Discriminator
--
-- Paper §3, Def 3.1: A discriminator is a grade-1 element d ∈ Λ¹V
-- paired with a predicate d: S → GF(2).
--
-- In our representation, a discriminator over population S with
-- vector space V = GF(2)^n is simply a vector in GF(2)^n together
-- with an evaluation function that maps it to a predicate on S.
------------------------------------------------------------------------

module CSTZ.Framework.Discriminator where

open import CSTZ.GF2
open import CSTZ.Vec

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

------------------------------------------------------------------------
-- Discrimination system: the evaluation pairing

-- A discrimination system consists of:
--   n : the dimension of the discriminator space V = GF(2)^n
--   S : the population type
--   eval : V → S → GF(2)   the evaluation pairing
--
-- We package this as a record so downstream modules can open it.

record DiscSystem : Set₁ where
  field
    dim  : ℕ                          -- n
    Pop  : Set                         -- S (the population)
    eval : GF2Vec dim → Pop → F        -- the evaluation pairing

  -- A discriminator is a vector in V
  Disc : Set
  Disc = GF2Vec dim

  -- Evaluate discriminator d on population element a
  _⟨_⟩ : Disc → Pop → F
  d ⟨ a ⟩ = eval d a

-- Don't open DiscSystem publicly here to avoid name clashes
-- when re-exported.  Users should open a specific DiscSystem value.

------------------------------------------------------------------------
-- Paper §3, Def 3.2: τ and σ as datum properties
--
-- τ and σ are two independent maps S → GF(2), representing the
-- two components of the membership profile.  In our representation,
-- a single discriminator d induces both via the evaluation pairing:
--   τ_d = eval d   (the "tau-side" predicate)
--   σ_d            (the "sigma-side" predicate)
--
-- The paper treats τ and σ as datum properties (attributes of
-- elements), not discriminator outputs.  In the formalization,
-- the distinction is captured by the two Pair roles in the
-- PFF Document model.  Here we simply define two evaluation
-- functions on a discriminator pair.

record DiscPair (sys : DiscSystem) : Set where
  open DiscSystem sys
  field
    d-τ : Disc   -- the τ-side discriminator
    d-σ : Disc   -- the σ-side discriminator

open DiscPair public
