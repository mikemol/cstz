------------------------------------------------------------------------
-- CSTZ.Sets.Russell
--
-- Paper §4, Thm 4.5: Exclusion of Russell's predicate.
-- [Axiom class AEP]
--
-- The Russell predicate P(x) = "x ∉ x" produces an affine τ-profile:
--   τ_{d_P}(0) = 1 ≠ 0
-- But a linear functional must send 0 to 0.  Therefore the Russell
-- predicate is not a valid discriminator under evaluation linearity.
--
-- Paper §4: "The predicate P(x) = (x ∉ x) does not produce a
-- non-trivial set under discriminative comprehension."
------------------------------------------------------------------------

module CSTZ.Sets.Russell where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Vec.Properties

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; module ≡-Reasoning)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- The key lemma: linear maps send 𝟎 to 𝟘
--
-- If eval is bilinear (P + E), then eval d 𝟎 = 0 for all d.
-- This is immediate from linearity in the second argument:
--   eval d (𝟎 + 𝟎) = eval d 𝟎 + eval d 𝟎
--   eval d 𝟎        = eval d 𝟎 + eval d 𝟎
-- Subtracting (i.e., adding, since -x = x over GF(2)):
--   0 = eval d 𝟎
--
-- We state this as a consequence of evaluation linearity.

-- Paper §4, Thm 4.5: Russell exclusion
--
-- If eval : GF2Vec n → GF2Vec n → F is bilinear (both profile
-- linearity and evaluation linearity hold), then there is no
-- discriminator d such that eval d 𝟎 = true.
--
-- Proof: by evaluation linearity,
--   eval d (𝟎 +V 𝟎) = eval d 𝟎 +F eval d 𝟎
-- But 𝟎 +V 𝟎 = 𝟎 (vector self-inverse), so:
--   eval d 𝟎 = eval d 𝟎 +F eval d 𝟎
--            = false   (by double-cancel)

russell-exclusion :
  ∀ {n : ℕ}
    (eval : GF2Vec n → GF2Vec n → F)
    -- Evaluation linearity (Axiom E):
    (eval-lin : ∀ d y₁ y₂ → eval d (y₁ +V y₂) ≡ eval d y₁ +F eval d y₂)
    (d : GF2Vec n)
  → eval d 𝟎 ≡ 𝟘
russell-exclusion {n} eval eval-lin d = begin
  eval d 𝟎                       ≡⟨ cong (eval d) (sym (+V-self 𝟎)) ⟩
  eval d (𝟎 +V 𝟎)                ≡⟨ eval-lin d 𝟎 𝟎 ⟩
  eval d 𝟎 +F eval d 𝟎           ≡⟨ double-cancel (eval d 𝟎) ⟩
  𝟘                               ∎
  where open ≡-Reasoning

-- Corollary: The Russell predicate, which would require
-- eval d_P 𝟎 = true (since P(0) = "0 ∉ 0" = true under the
-- Russell construction), is incompatible with evaluation linearity.
--
-- Any eval satisfying E has eval d 𝟎 = false for all d.
-- The Russell predicate needs eval d_P 𝟎 = true.
-- Contradiction.

-- Helper: true ≢ false
private
  true≢false : 𝟙 ≡ 𝟘 → ⊥
  true≢false ()

russell-contradiction :
  ∀ {n : ℕ}
    (eval : GF2Vec n → GF2Vec n → F)
    (eval-lin : ∀ d y₁ y₂ → eval d (y₁ +V y₂) ≡ eval d y₁ +F eval d y₂)
    (d : GF2Vec n)
  → eval d 𝟎 ≡ 𝟙 → ⊥
russell-contradiction eval eval-lin d eq =
  true≢false (trans (sym eq) (russell-exclusion eval eval-lin d))
