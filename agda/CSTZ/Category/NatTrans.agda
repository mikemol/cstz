------------------------------------------------------------------------
-- CSTZ.Category.NatTrans
--
-- Paper §6, Def 6.12: Natural transformation.  [A]
--
-- A natural transformation α: F ⇒ G between functors (κ-deformations)
-- is a coherent family of morphisms: for each object A, a morphism
-- α_A: F(A) → G(A) such that the naturality square commutes.
------------------------------------------------------------------------

module CSTZ.Category.NatTrans where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Category.Functor

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §6, Def 6.12

-- A natural transformation between two DiscFunctors.
-- At the discriminator level: a family of grade-1 elements
-- indexed by objects (κ-equivalence classes) satisfying naturality.

record NatTrans {n n' : ℕ} (F G : DiscFunctor n n') : Set where
  field
    -- For each discriminator d in the source, a morphism component
    component : GF2Vec n → GF2Vec n'

    -- Naturality: for all d,
    -- component d +V G.mapDisc d = F.mapDisc d +V component d
    -- (over GF(2), this simplifies because + is commutative)
    naturality : ∀ (d : GF2Vec n)
      → component d +V DiscFunctor.mapDisc G d
        ≡ DiscFunctor.mapDisc F d +V component d

-- Paper §6, Prop 6.13:
-- "Naturality follows from the ring homomorphism property."
-- Since both F and G preserve the wedge product, and the component
-- maps are linear (grade-1 elements), the naturality square commutes
-- by linearity of the exterior algebra.
