------------------------------------------------------------------------
-- CSTZ.Vec.Properties
--
-- Properties of GF(2)^n vector spaces: additive group structure,
-- basis vector properties, inner product bilinearity, and the
-- zero-map-zero lemma that drives Russell exclusion.
--
-- Paper §2, §4 (bilinear form for Russell exclusion)
------------------------------------------------------------------------

module CSTZ.Vec.Properties where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; zipWith ; replicate ; tabulate ; lookup ; map)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Vector addition forms an abelian group

-- Left identity: 𝟎 + v = v
+V-identityˡ : ∀ {n} (v : GF2Vec n) → 𝟎 +V v ≡ v
+V-identityˡ []       = refl
+V-identityˡ (x ∷ xs) = cong₂ _∷_ (+F-identityˡ x) (+V-identityˡ xs)

-- Right identity: v + 𝟎 = v
+V-identityʳ : ∀ {n} (v : GF2Vec n) → v +V 𝟎 ≡ v
+V-identityʳ []       = refl
+V-identityʳ (x ∷ xs) = cong₂ _∷_ (+F-identityʳ x) (+V-identityʳ xs)

-- Self-inverse: v + v = 𝟎  (characteristic 2)
+V-self : ∀ {n} (v : GF2Vec n) → v +V v ≡ 𝟎
+V-self []       = refl
+V-self (x ∷ xs) = cong₂ _∷_ (double-cancel x) (+V-self xs)

-- Commutativity: u + v = v + u
+V-comm : ∀ {n} (u v : GF2Vec n) → u +V v ≡ v +V u
+V-comm []       []       = refl
+V-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (+F-comm x y) (+V-comm xs ys)

-- Associativity: (u + v) + w = u + (v + w)
+V-assoc : ∀ {n} (u v w : GF2Vec n) → (u +V v) +V w ≡ u +V (v +V w)
+V-assoc []       []       []       = refl
+V-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (+F-assoc x y z) (+V-assoc xs ys zs)

-- Cancellation: u + v = 𝟎  implies  u = v
+V-cancel : ∀ {n} {u v : GF2Vec n} → u +V v ≡ 𝟎 → u ≡ v
+V-cancel {_} {[]}     {[]}     _  = refl
+V-cancel {_} {x ∷ xs} {y ∷ ys} eq =
  cong₂ _∷_ (+F-cancel (head-eq eq)) (+V-cancel (tail-eq eq))
  where
    head-eq : ∀ {n} {a b : F} {as bs : Vec F n} → (a ∷ as) ≡ (b ∷ bs) → a ≡ b
    head-eq refl = refl
    tail-eq : ∀ {n} {a b : F} {as bs : Vec F n} → (a ∷ as) ≡ (b ∷ bs) → as ≡ bs
    tail-eq refl = refl

------------------------------------------------------------------------
-- Inner product properties

-- ⟨𝟎, v⟩ = 0
·V-zeroˡ : ∀ {n} (v : GF2Vec n) → 𝟎 ·V v ≡ 𝟘
·V-zeroˡ []       = refl
·V-zeroˡ (x ∷ xs) = begin
  (𝟘 ·F x) +F (𝟎 ·V xs)  ≡⟨ cong₂ _+F_ (·F-zeroˡ x) (·V-zeroˡ xs) ⟩
  𝟘 +F 𝟘                  ≡⟨ refl ⟩
  𝟘                        ∎

-- ⟨v, 𝟎⟩ = 0
·V-zeroʳ : ∀ {n} (v : GF2Vec n) → v ·V 𝟎 ≡ 𝟘
·V-zeroʳ []       = refl
·V-zeroʳ (x ∷ xs) = begin
  (x ·F 𝟘) +F (xs ·V 𝟎)  ≡⟨ cong₂ _+F_ (·F-zeroʳ x) (·V-zeroʳ xs) ⟩
  𝟘 +F 𝟘                  ≡⟨ refl ⟩
  𝟘                        ∎

-- Bilinearity in first argument: ⟨u + v, w⟩ = ⟨u,w⟩ + ⟨v,w⟩
-- Paper §4: This is profile linearity instantiated at the vector level.
-- Helper: rearrange (a+b)+(c+d) = (a+c)+(b+d) over GF(2)
private
  +F-interchange : ∀ (a b c d : F) → (a +F b) +F (c +F d) ≡ (a +F c) +F (b +F d)
  +F-interchange a b c d = begin
    (a +F b) +F (c +F d)    ≡⟨ +F-assoc a b (c +F d) ⟩
    a +F (b +F (c +F d))    ≡⟨ cong (a +F_) (sym (+F-assoc b c d)) ⟩
    a +F ((b +F c) +F d)    ≡⟨ cong (λ x → a +F (x +F d)) (+F-comm b c) ⟩
    a +F ((c +F b) +F d)    ≡⟨ cong (a +F_) (+F-assoc c b d) ⟩
    a +F (c +F (b +F d))    ≡⟨ sym (+F-assoc a c (b +F d)) ⟩
    (a +F c) +F (b +F d)    ∎

·V-linearˡ : ∀ {n} (u v w : GF2Vec n)
  → (u +V v) ·V w ≡ (u ·V w) +F (v ·V w)
·V-linearˡ []       []       []       = refl
·V-linearˡ (a ∷ as) (b ∷ bs) (c ∷ cs) = begin
  ((a +F b) ·F c) +F ((as +V bs) ·V cs)
    ≡⟨ cong (_+F ((as +V bs) ·V cs)) (·F-distribʳ-+F c a b) ⟩
  ((a ·F c) +F (b ·F c)) +F ((as +V bs) ·V cs)
    ≡⟨ cong (((a ·F c) +F (b ·F c)) +F_) (·V-linearˡ as bs cs) ⟩
  ((a ·F c) +F (b ·F c)) +F ((as ·V cs) +F (bs ·V cs))
    ≡⟨ +F-interchange (a ·F c) (b ·F c) (as ·V cs) (bs ·V cs) ⟩
  ((a ·F c) +F (as ·V cs)) +F ((b ·F c) +F (bs ·V cs))
    ∎

-- Bilinearity in second argument: ⟨u, v + w⟩ = ⟨u,v⟩ + ⟨u,w⟩
·V-linearʳ : ∀ {n} (u v w : GF2Vec n)
  → u ·V (v +V w) ≡ (u ·V v) +F (u ·V w)
·V-linearʳ []       []       []       = refl
·V-linearʳ (a ∷ as) (b ∷ bs) (c ∷ cs) = begin
  (a ·F (b +F c)) +F (as ·V (bs +V cs))
    ≡⟨ cong₂ _+F_ (·F-distribˡ-+F a b c) (·V-linearʳ as bs cs) ⟩
  ((a ·F b) +F (a ·F c)) +F ((as ·V bs) +F (as ·V cs))
    ≡⟨ +F-interchange (a ·F b) (a ·F c) (as ·V bs) (as ·V cs) ⟩
  ((a ·F b) +F (as ·V bs)) +F ((a ·F c) +F (as ·V cs))
    ∎

------------------------------------------------------------------------
-- Key lemma for Russell exclusion (Paper §4, Thm 4.5):
-- A linear map sends 𝟎 to 𝟘.
-- The Russell predicate sends 𝟎 to 𝟙, so it's not linear.

linear-map-zero : ∀ {n} (v : GF2Vec n) → v ·V 𝟎 ≡ 𝟘
linear-map-zero = ·V-zeroʳ
