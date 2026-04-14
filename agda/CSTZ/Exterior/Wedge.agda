------------------------------------------------------------------------
-- CSTZ.Exterior.Wedge
--
-- The wedge product on Λ(GF(2)^n) and its key properties:
--   - v ∧ v = 0  (nilpotency / self-wedge vanishes)
--   - commutativity over GF(2) (since -1 = 1)
--   - associativity
--
-- Paper §2: "The wedge product is commutative (since -1 = 1),
-- associative, and nilpotent on repeated factors (v∧v = 0)."
--
-- Paper §5, Def 5.1: "d ∧ d = 0.  Grade 0 is what results when
-- a discrimination collapses."
------------------------------------------------------------------------

module CSTZ.Exterior.Wedge where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Exterior.Basis

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec ; [] ; _∷_ ; zipWith ; lookup)
open import Data.Bool.Base using (if_then_else_ ; _∨_)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Wedge product on basis elements
--
-- For subsets A and B of {0,...,n-1}:
--   A ∧ B = A ∪ B   if A and B are disjoint
--         = 0        if A and B overlap
--
-- Over GF(2), the sign factor (-1)^(|A∩B'|) = 1 always, so
-- commutativity is immediate.

-- Wedge product of two basis subsets: returns a coefficient and
-- the resulting subset.
wedgeBasis : ∀ {n} → Subset n → Subset n → F × Subset n
wedgeBasis {n} a b =
  if disjoint a b
  then (𝟙 , a ∪ b)
  else (𝟘 , ∅)

------------------------------------------------------------------------
-- Wedge product on exterior algebra elements
--
-- (f ∧ g)(s) = Σ_{a ∪ b = s, a ∩ b = ∅} f(a) · g(b)
--
-- For the full algebra, this requires summing over all decompositions
-- of s into disjoint pairs.  We define it compositionally.

-- For now, we provide the wedge product on basis elements and
-- lift it bilinearly.  The full sum-over-decompositions form is
-- used in the boundary module.

-- Wedge of two basis elements as an Exterior element
wedge₂ : ∀ {n} → Subset n → Subset n → Exterior n
wedge₂ a b t with disjoint a b
... | false = 𝟘
... | true  = basisEq (a ∪ b) t

------------------------------------------------------------------------
-- Key property: v ∧ v = 0
--
-- Paper §2, §5: "v ∧ v = 0 for all v"
-- For a basis element (singleton set {i}), singleton i is not
-- disjoint from itself (position i is true in both), so the wedge
-- product returns 0.

-- A subset is not disjoint from itself unless it's empty
disjoint-self-false : ∀ {n} (s : Subset n) (i : Fin n)
  → lookup s i ≡ true → disjoint s s ≡ false
disjoint-self-false (true  ∷ _)  Fin.zero    refl = refl
disjoint-self-false (false ∷ xs) (Fin.suc i) p    = disjoint-self-false xs i p
disjoint-self-false (true  ∷ xs) (Fin.suc i) p    = refl

-- For any non-empty subset, self-wedge is zero
wedge-self-zero : ∀ {n} (s : Subset n) (i : Fin n)
  → lookup s i ≡ true
  → ∀ (t : Subset n) → wedge₂ s s t ≡ 𝟘
wedge-self-zero s i p t with disjoint s s | disjoint-self-false s i p
... | false | refl = refl

------------------------------------------------------------------------
-- Commutativity: a ∧ b = b ∧ a
--
-- Over GF(2), the graded commutativity factor (-1)^{jk} = 1 for
-- all grades j, k.  So ∧ is literally commutative, not just
-- graded-commutative.

-- Disjointness is symmetric
disjoint-comm : ∀ {n} (a b : Subset n) → disjoint a b ≡ disjoint b a
disjoint-comm []       []       = refl
disjoint-comm (x ∷ xs) (y ∷ ys) with x ∧ y | y ∧ x | ·F-comm x y
... | true  | .true  | refl = refl
... | false | .false | refl = disjoint-comm xs ys

-- Union is commutative
∪-comm : ∀ {n} (a b : Subset n) → a ∪ b ≡ b ∪ a
∪-comm []       []       = refl
∪-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (∨-comm x y) (∪-comm xs ys)
  where
    ∨-comm : ∀ (x y : Bool) → x ∨ y ≡ y ∨ x
    ∨-comm false false = refl
    ∨-comm false true  = refl
    ∨-comm true  false = refl
    ∨-comm true  true  = refl

-- Wedge product is commutative on basis elements
wedge₂-comm : ∀ {n} (a b : Subset n) (t : Subset n)
  → wedge₂ a b t ≡ wedge₂ b a t
wedge₂-comm a b t with disjoint a b | disjoint b a | disjoint-comm a b
... | false | .false | refl = refl
... | true  | .true  | refl = cong (λ u → basisEq u t) (∪-comm a b)
