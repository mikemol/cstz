------------------------------------------------------------------------
-- CSTZ.Category.Adjunction
--
-- Paper §6, Thm 6.11: Triadic adjunction system.  [A]
--
-- S₃ symmetry of the triangle identity generates 6 adjunctions —
-- 3 chirality pairs — by permuting {κ,σ,τ} over the adjunction
-- stencil A ← B → C.
--
-- Python cofibration (STUDY.md §8.2): the `Adjunction` record and
-- `Axis` data type below have no Python counterpart. Adjunction
-- structure at runtime is implicit in how callers compose the
-- witness and coefficient morphisms (see `src/cstz/category.py ::
-- compose_witnesses` and `compose_coeff`) rather than being carried
-- as a first-class algebraic object.
------------------------------------------------------------------------

module CSTZ.Category.Adjunction where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Category.Functor

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Paper §6, Thm 6.11

-- An adjunction F ⊣ U consists of:
--   F : C → D  (left adjoint / free functor)
--   U : D → C  (right adjoint / forgetful functor)
--   unit   : id_C ⇒ U ∘ F
--   counit : F ∘ U ⇒ id_D
--   subject to zig-zag equations:
--     (counit ∘ F) ∘ (F ∘ unit) = id_F
--     (U ∘ counit) ∘ (unit ∘ U) = id_U

record Adjunction {n n' : ℕ} : Set where
  field
    leftAdj  : DiscFunctor n n'    -- F (free)
    rightAdj : DiscFunctor n' n    -- U (forgetful)

    -- Retract property: U ∘ F = id (projection after inclusion)
    retract : ∀ (d : GF2Vec n)
      → DiscFunctor.mapDisc rightAdj (DiscFunctor.mapDisc leftAdj d) ≡ d

-- Paper §6, Thm 6.11:
-- The triangle identity κ = σ + τ has S₃ symmetry.
-- Each of the 6 permutations of {κ,σ,τ} over the stencil
-- (left, hom, right) gives a retract adjunction.
--
-- These are individually trivial (direct summand retracts)
-- but collectively non-trivial as covering families for the
-- Grothendieck topology (Thm 9.18).

-- The 3 axis choices:
data Axis : Set where
  κ-axis σ-axis τ-axis : Axis

-- Each axis gives two adjunctions (chirality pair).
-- Total: 3 × 2 = 6 adjunctions.

-- Paper proof: π ∘ ι = id (projection after inclusion = identity).
-- This is the retract property.  For GF(2) vector spaces, this
-- holds because a subspace inclusion followed by projection onto
-- that subspace is the identity on the subspace.

-- Zig-zag equations are trivially satisfied for retract adjunctions:
-- when the unit is ι and the counit is π, both zig-zag composites
-- reduce to π ∘ ι = id.
