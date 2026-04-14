------------------------------------------------------------------------
-- CSTZ.Vec
--
-- Vector spaces over GF(2), represented as Vec Bool n.
--
-- Paper §2: "V = GF(2)^n is the n-dimensional vector space over
-- GF(2).  Pointwise xor gives vector addition; the standard basis
-- {e₁,...,eₙ} spans V."
------------------------------------------------------------------------

module CSTZ.Vec where

open import CSTZ.GF2

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec
  using (Vec ; [] ; _∷_ ; zipWith ; replicate ; tabulate ; lookup ; map ; foldr)
  public
open import Data.Vec using (head ; tail)
open import Data.Bool.Base using (if_then_else_)
open import Relation.Nullary using (does)
open import Data.Fin.Properties using (_≟_)

------------------------------------------------------------------------
-- Type alias: a vector in GF(2)^n

GF2Vec : ℕ → Set
GF2Vec n = Vec F n

------------------------------------------------------------------------
-- Vector operations

-- Zero vector
𝟎 : ∀ {n} → GF2Vec n
𝟎 = replicate _ 𝟘

-- Vector addition (pointwise xor)
_+V_ : ∀ {n} → GF2Vec n → GF2Vec n → GF2Vec n
_+V_ = zipWith _+F_

infixl 6 _+V_

-- Scalar multiplication (pointwise and)
_*V_ : F → ∀ {n} → GF2Vec n → GF2Vec n
c *V v = map (c ·F_) v

infixl 7 _*V_

-- Standard basis vector: e i has true at position i, false elsewhere
e : ∀ {n} → Fin n → GF2Vec n
e i = tabulate (λ j → does (i ≟ j))

-- Inner product (dot product over GF(2))
-- ⟨u,v⟩ = Σᵢ uᵢ · vᵢ
_·V_ : ∀ {n} → GF2Vec n → GF2Vec n → F
_·V_ {zero}  []       []       = 𝟘
_·V_ {suc n} (x ∷ xs) (y ∷ ys) = (x ·F y) +F (xs ·V ys)

infixl 7 _·V_

------------------------------------------------------------------------
-- Linear functional: a map GF2Vec n → F
-- Over GF(2), every linear functional is dot product with some vector.

LinearFunc : ℕ → Set
LinearFunc n = GF2Vec n → F

-- Every vector induces a linear functional via dot product
toLinear : ∀ {n} → GF2Vec n → LinearFunc n
toLinear v = v ·V_

-- Note: the membership profile type (F × F) is defined in
-- CSTZ.Framework.Profile, not here, to avoid name clashes.
