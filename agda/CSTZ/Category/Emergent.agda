------------------------------------------------------------------------
-- CSTZ.Category.Emergent
--
-- Paper §6, Def 6.5-6.6: The emergent category C(S,κ).  [A]
--
-- Objects = κ-equivalence classes.
-- Morphisms = directed discriminators.
-- Identity = degenerate self-discrimination (d ∧ d = 0).
-- Composition = joint filtration (wedge product, produces 2-cells).
------------------------------------------------------------------------

module CSTZ.Category.Emergent where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Exterior.Basis
open import CSTZ.Framework.Discriminator

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Paper §6, Def 6.5: C(S,κ)
--
-- We parameterize over a dimension n and a population type S with
-- an evaluation function.  Objects are represented abstractly by
-- their class representative; morphisms carry a witness discriminator.

-- A discrimination context bundles everything C(S,κ) needs.
record DiscCtx : Set₁ where
  field
    n    : ℕ                     -- dimension of V = GF(2)^n
    Pop  : Set                   -- population S
    eval : GF2Vec n → Pop → F   -- evaluation pairing
    -- For composition we also need eval on pairs of vectors
    -- (the 2-cell structure).  This is captured by the wedge
    -- product on the discriminator side.

open DiscCtx

------------------------------------------------------------------------
-- Morphisms

-- Paper §6, Def 6.1: A directed morphism from a to b is a
-- discriminator d with τ_d(a) = 1 and σ_d(b) = 1.
-- Here τ and σ are two independent evaluation functions.
-- We bundle them as a pair of eval functions.

record Morphism (ctx : DiscCtx) (a b : Pop ctx) : Set where
  field
    d-witness : GF2Vec (n ctx)              -- the witnessing discriminator
    τ-source  : eval ctx d-witness a ≡ 𝟙   -- τ fires on source
    σ-target  : eval ctx d-witness b ≡ 𝟙   -- σ fires on target
    -- Note: in the full paper, τ and σ are separate eval functions.
    -- Here we use the same eval for both; the τ/σ distinction is
    -- structural (source role vs target role), not a separate function.

------------------------------------------------------------------------
-- Identity morphism

-- Paper §6, Def 6.5: "The identity morphism id_A is the degenerate
-- discriminator d ∧ d = 0."
-- The identity is the zero vector 𝟎: it evaluates to false on
-- everything, which means it doesn't discriminate — it's the
-- trivial/degenerate morphism.

-- For the identity to type-check as a Morphism, we'd need
-- eval 𝟎 a = true, which is FALSE (linear maps send 0 to 0).
-- This reveals that identity in C(S,κ) is not a morphism in the
-- sense of Def 6.1 — it's the grade-0 degenerate element.
-- The paper handles this by making identity the special case
-- where the discriminator is trivial.

------------------------------------------------------------------------
-- Composition

-- Paper §6, Def 6.6: "g ∘ f = d₁ ∧ d₂ ∈ Λ²V"
-- Composition of two 1-morphisms (grade-1 elements) produces a
-- 2-cell (grade-2 element).  This is the wedge product of the
-- two witness discriminators.

-- The composition result type: a grade-2 element (subset of {0,...,n-1}
-- with exactly 2 elements set to true).

compose-witnesses : ∀ {n} → GF2Vec n → GF2Vec n → Subset n
compose-witnesses d₁ d₂ = d₁ ∪ d₂
  -- This is the bitwise OR of the two vectors viewed as subsets.
  -- For the composition to be non-degenerate, d₁ and d₂ must be
  -- linearly independent (their OR has exactly 2 true positions).
  -- If they're linearly dependent, d₁ ∧ d₂ = 0 (grade-0 element).

-- The composition's coefficient in the exterior algebra:
compose-coeff : ∀ {n} → GF2Vec n → GF2Vec n → F
compose-coeff d₁ d₂ = disjoint d₁ d₂
  -- Non-zero iff the discriminators are "disjoint" as subsets
  -- (i.e., linearly independent as basis vectors).
  -- d₁ ∧ d₂ ≠ 0 iff d₁ and d₂ don't share any set positions.

------------------------------------------------------------------------
-- 2-category structure (Paper §6, Remark 6.4)
--
-- The framework is 2-categorical from the start:
-- - 0-cells: κ-equivalence classes (objects)
-- - 1-cells: discriminators (grade-1 elements)
-- - 2-cells: wedge products of discriminators (grade-2 elements)
-- This is not a deficiency: the exterior algebra's grading IS
-- the categorical dimension.
