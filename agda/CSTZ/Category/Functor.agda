------------------------------------------------------------------------
-- CSTZ.Category.Functor
--
-- Paper §6, Def 6.9 + Prop 6.10: Functors as κ-deformations.  [A]
--
-- A functor F: C(S,κ) → C(S',κ') is a structure-preserving map
-- that sends discriminators to discriminators and preserves the
-- wedge product and τ/σ assignments.
--
-- Forgetful functor: projection π: κ → κ' (omitting dimensions).
-- Free functor: inclusion ι: κ' ↪ κ (embedding into finer regime).
------------------------------------------------------------------------

module CSTZ.Category.Functor where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Exterior.Basis

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §6, Def 6.9: Functor

-- A functor between discrimination categories is a linear map
-- on discriminator spaces that preserves the wedge product
-- (ring homomorphism of exterior algebras) and τ/σ assignments.

record DiscFunctor (n n' : ℕ) : Set where
  field
    -- The map on discriminators (grade-1 elements)
    mapDisc : GF2Vec n → GF2Vec n'

    -- Linearity: mapDisc (d₁ + d₂) = mapDisc d₁ + mapDisc d₂
    map-linear : ∀ (d₁ d₂ : GF2Vec n)
      → mapDisc (d₁ +V d₂) ≡ mapDisc d₁ +V mapDisc d₂

    -- Preservation of zero: mapDisc 𝟎 = 𝟎
    map-zero : mapDisc 𝟎 ≡ 𝟎

    -- Wedge preservation: mapDisc d₁ ∧ mapDisc d₂ = map(d₁ ∧ d₂)
    -- (This follows from linearity for exterior algebras over fields,
    -- but we state it as a field for clarity.)
    map-wedge : ∀ (d₁ d₂ : GF2Vec n)
      → disjoint (mapDisc d₁) (mapDisc d₂)
        ≡ disjoint d₁ d₂

------------------------------------------------------------------------
-- Paper §6, Prop 6.10: Forgetful and free functors

-- (i) Forgetful functor: projection from finer to coarser.
-- Given κ' ⊂ κ, the projection π drops the extra dimensions.
-- For vectors: project by zeroing out the dropped coordinates.

-- (ii) Free functor: inclusion from coarser to finer.
-- Given κ' ⊂ κ, the inclusion ι embeds by adding zero coordinates.

-- For GF(2)^n → GF(2)^m with m ≤ n:
-- Projection: take the first m coordinates.
-- Inclusion: pad with zeros.

open import Data.Vec using (Vec ; take ; _++_ ; replicate)

project : ∀ {n} (m : ℕ) → GF2Vec (m Data.Nat.+ n) → GF2Vec m
project m v = take m v
  where open import Data.Nat using (_+_)

include : ∀ {n} (m : ℕ) → GF2Vec m → GF2Vec (m Data.Nat.+ n)
include {n} m v = v ++ replicate n 𝟘
  where open import Data.Nat using (_+_)

-- Paper §6, Prop 6.10 proof:
-- "π is a ring homomorphism of exterior algebras"
-- "π ∘ ι = id" (projection after inclusion is identity)
-- These together give the retract adjunction F ⊣ U.
