------------------------------------------------------------------------
-- CSTZ.Examples.GF2Cubed.Sets
--
-- Paper App E, §4: Set-theoretic consequences at GF(2)³.
------------------------------------------------------------------------

module CSTZ.Examples.GF2Cubed.Sets where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Vec.Properties
open import CSTZ.Examples.GF2Cubed.Setup

open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; _≢_)

------------------------------------------------------------------------
-- Thm 4.2: Extensionality — each element has unique profile at κ₃

-- All 8 profiles are distinct (each aᵢ IS its own profile vector).
-- We verify a few representative distinctness checks.
ext-a₀≢a₁ : a₀ ≢ a₁
ext-a₀≢a₁ ()

ext-a₃≢a₅ : a₃ ≢ a₅
ext-a₃≢a₅ ()

------------------------------------------------------------------------
-- Thm 4.5: Russell exclusion

-- The Russell predicate dP(a) = 1 + a·a  is affine.
-- dP(a₀) = 1 + 0·0 = 1 + 0 = 1
russell-at-zero : 𝟙 +F (a₀ ·V a₀) ≡ 𝟙
russell-at-zero = refl

-- But linearity requires dP(0) = 0.  Since dP(0) = 1 ≠ 0, excluded.
-- (This is the concrete instance of Sets.Russell.russell-exclusion.)

-- Also: dP(a₀ + a₀) = dP(0) = 1
-- But dP(a₀) + dP(a₀) = 1 + 1 = 0.  Linearity violated.
russell-nonlinear : (𝟙 +F (a₀ ·V a₀)) +F (𝟙 +F (a₀ ·V a₀)) ≡ 𝟘
russell-nonlinear = refl

------------------------------------------------------------------------
-- Prop 4.18: Pairing {a₄, a₆}

-- Difference: a₄ + a₆ = 100 + 110 = 010 = e₂
pairing-diff : a₄ +V a₆ ≡ e₂
pairing-diff = refl

-- Under κ = ⟨e₁, e₃⟩: e₂ ∈ κ⊥ (e₁·e₂ = 0, e₃·e₂ = 0)
pair-annihilator-e₁ : eval e₁ (a₄ +V a₆) ≡ 𝟘
pair-annihilator-e₁ = refl

pair-annihilator-e₃ : eval e₃ (a₄ +V a₆) ≡ 𝟘
pair-annihilator-e₃ = refl

-- Both discriminators agree on a₄ and a₆:
pair-e₁-agree : eval e₁ a₄ ≡ eval e₁ a₆
pair-e₁-agree = refl

pair-e₃-agree : eval e₃ a₄ ≡ eval e₃ a₆
pair-e₃-agree = refl

-- But a₀ is separated from a₄:
pair-separated : eval e₁ a₀ ≢ eval e₁ a₄
pair-separated ()

------------------------------------------------------------------------
-- Thm 4.13: Foundation chain bound

-- Chain a₇ ∋ a₃ ∋ a₁:
-- Link v₁ = a₇ + a₃ = 111 + 011 = 100 = e₁
link-v₁ : a₇ +V a₃ ≡ e₁
link-v₁ = refl

-- Link v₂ = a₃ + a₁ = 011 + 001 = 010 = e₂
link-v₂ : a₃ +V a₁ ≡ e₂
link-v₂ = refl

-- Links are linearly independent (e₁ ≠ e₂)
links-indep : e₁ ≢ e₂
links-indep ()

-- Chain depth = 2 ≤ 3 = dim(V).  ✓

-- Maximum chain: a₇ ∋ a₃ ∋ a₁ ∋ a₀ (depth 3)
link-v₃ : a₁ +V a₀ ≡ e₃
link-v₃ = refl

------------------------------------------------------------------------
-- Thm 4.33: Finite choice

-- Family S₁ = {a₀,a₁}, S₂ = {a₄,a₅}.
-- Under κ₁ = ⟨e₁⟩: unresolved (e₁ agrees within each family).
choice-unresolved-S₁ : eval e₁ a₀ ≡ eval e₁ a₁
choice-unresolved-S₁ = refl

choice-unresolved-S₂ : eval e₁ a₄ ≡ eval e₁ a₅
choice-unresolved-S₂ = refl

-- Evolve: add e₃.  Now resolved.
choice-resolved-S₁ : eval e₃ a₀ ≢ eval e₃ a₁
choice-resolved-S₁ ()

choice-resolved-S₂ : eval e₃ a₄ ≢ eval e₃ a₅
choice-resolved-S₂ ()

------------------------------------------------------------------------
-- Prop 4.19: Symmetric difference

-- (e₁+e₂)(a₂) = 0+1 = 1
symdiff-a₂ : eval e₁+e₂ a₂ ≡ 𝟙
symdiff-a₂ = refl

-- (e₁+e₂)(a₆) = 1+1 = 0
symdiff-a₆ : eval e₁+e₂ a₆ ≡ 𝟘
symdiff-a₆ = refl

------------------------------------------------------------------------
-- Prop 4.26: Indistinguishability

-- Under κ₂ = ⟨e₁,e₂⟩: a₀ and a₁ are indistinguishable.
indist-e₁ : eval e₁ a₀ ≡ eval e₁ a₁
indist-e₁ = refl

indist-e₂ : eval e₂ a₀ ≡ eval e₂ a₁
indist-e₂ = refl

-- Their difference: a₀ + a₁ = 001 = e₃ ∈ κ₂⊥
indist-diff : a₀ +V a₁ ≡ e₃
indist-diff = refl
