------------------------------------------------------------------------
-- CSTZ.Monoidal.Product
--
-- Paper §8, Def 8.1: Monoidal product from ∧.  [A]
--
-- A ⊗ B = joint discrimination profile.
-- f ⊗ g witnessed by d_f ∧ d_g (parallel composition).
------------------------------------------------------------------------

module CSTZ.Monoidal.Product where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Exterior.Basis

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Paper §8, Def 8.1

-- The monoidal product of two objects A and B is their joint
-- discrimination profile: the object A ⊗ B whose τ/σ profile
-- under each discriminator d is determined by simultaneously
-- applying d to both A and B.

-- For morphisms: the monoidal product of f: A → B (witnessed by d_f)
-- and g: C → D (witnessed by d_g) is f ⊗ g: A⊗C → B⊗D, witnessed
-- by the wedge product d_f ∧ d_g.

-- At the vector level: d_f ⊗ d_g corresponds to the union of the
-- two witness subsets, when they are disjoint.

_⊗-witness_ : ∀ {n} → GF2Vec n → GF2Vec n → Subset n
d₁ ⊗-witness d₂ = d₁ ∪ d₂

-- The coefficient: non-zero iff the two witnesses are "disjoint"
-- (don't share set positions).
_⊗-coeff_ : ∀ {n} → GF2Vec n → GF2Vec n → F
d₁ ⊗-coeff d₂ = disjoint d₁ d₂

-- Paper §8, Remark:
-- "The monoidal product (parallel composition) and categorical
-- composition (sequential composition) are both mediated by the
-- wedge product, but they differ in the τ/σ choreography.
-- Sequential composition requires the intermediate object to appear
-- on opposite sides (σ of first, τ of second).
-- Parallel composition imposes no matching condition."
