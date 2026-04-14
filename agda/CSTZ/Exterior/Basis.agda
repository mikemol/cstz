------------------------------------------------------------------------
-- CSTZ.Exterior.Basis
--
-- Basis elements for the exterior algebra Λ^k(GF(2)^n).
--
-- Over GF(2), basis elements of Λ^k correspond to k-element subsets
-- of {0,...,n-1}.  We represent these as characteristic functions
-- (Vec Bool n) with exactly k true entries.  An element of Λ^k is
-- a GF(2)-linear combination of such basis elements.
--
-- This representation is computationally concrete: wedge products
-- are pointwise OR with a disjointness check, and ∂ drops each
-- true position in turn.
--
-- Paper §2: "Λ(GF(2)^n) = ⊕ₖ Λ^k(GF(2)^n)"
------------------------------------------------------------------------

module CSTZ.Exterior.Basis where

open import CSTZ.GF2

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc ; toℕ)
open import Data.Vec using (Vec ; [] ; _∷_ ; zipWith ; replicate ;
                            tabulate ; lookup ; map ; foldr ; count)
open import Data.Bool.Base using (if_then_else_ ; _∨_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Subset representation

-- A subset of {0,...,n-1} as a characteristic vector.
Subset : ℕ → Set
Subset n = Vec Bool n

-- The empty subset
∅ : ∀ {n} → Subset n
∅ = replicate _ false

-- Singleton subset containing just index i
singleton : ∀ {n} → Fin n → Subset n
singleton i = tabulate (λ j → does (i ≟F j))
  where
    open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
    open import Relation.Nullary using (does)

-- Union of two subsets (pointwise or)
_∪_ : ∀ {n} → Subset n → Subset n → Subset n
_∪_ = zipWith _∨_

-- Are two subsets disjoint? (no position is true in both)
disjoint : ∀ {n} → Subset n → Subset n → Bool
disjoint []       []       = true
disjoint (x ∷ xs) (y ∷ ys) = if (x ∧ y) then false else disjoint xs ys

-- Cardinality (number of true entries)
card : ∀ {n} → Subset n → ℕ
card [] = 0
card (true  ∷ xs) = suc (card xs)
card (false ∷ xs) = card xs

-- Membership test
_∈S_ : ∀ {n} → Fin n → Subset n → Bool
i ∈S s = lookup s i

------------------------------------------------------------------------
-- Grade-k elements of the exterior algebra
--
-- An element of Λ^k(GF(2)^n) is a function from k-element subsets
-- to GF(2).  We represent this as a function from ALL subsets to
-- GF(2), with the understanding that it's zero on subsets of
-- cardinality ≠ k.  This avoids needing to enumerate k-subsets
-- explicitly while keeping the algebra simple.
--
-- For efficiency and concreteness, we also define a "graded element"
-- that bundles the grade with the coefficient function.

-- A general element of the exterior algebra (ungraded):
-- assigns a GF(2) coefficient to each subset.
Exterior : ℕ → Set
Exterior n = Subset n → F

-- Zero element
𝟎E : ∀ {n} → Exterior n
𝟎E _ = 𝟘

-- Addition (pointwise xor)
_+E_ : ∀ {n} → Exterior n → Exterior n → Exterior n
(f +E g) s = f s +F g s

infixl 6 _+E_

-- Basis element: the element that is 1 on exactly subset s, 0 elsewhere.
-- Over GF(2), "decidable equality on subsets" is just pointwise Bool equality.
basisEq : ∀ {n} → Subset n → Subset n → Bool
basisEq []       []       = true
basisEq (x ∷ xs) (y ∷ ys) = (eqBool x y) ∧ basisEq xs ys
  where
    eqBool : Bool → Bool → Bool
    eqBool false false = true
    eqBool true  true  = true
    eqBool _     _     = false

-- Basis element at subset s: coefficient 1 on s, 0 on everything else
basis : ∀ {n} → Subset n → Exterior n
basis s t = basisEq s t
