------------------------------------------------------------------------
-- CSTZ.Verification.PairingBilinear
--
-- Paper App B.32: Pairing as equivalence class, not characteristic
-- function.  [Axiom class A]
--
-- The pair {a,b} is defined by a+b ∈ κ⊥ (annihilator), NOT by
-- a characteristic function χ_{a,b}.  No linear "is a or is b"
-- predicate is needed.
------------------------------------------------------------------------

module CSTZ.Verification.PairingBilinear where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Vec.Properties

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

------------------------------------------------------------------------
-- The key insight (Paper B.32):
--
-- Over GF(2), the characteristic function χ_{a,b}(x) = 1 iff x ∈ {a,b}
-- is NOT linear in general.  For {a,b} with a ≠ b:
--   χ(a) = 1, χ(b) = 1, χ(a+b) = ?
-- If a+b ∉ {a,b}, then χ(a+b) = 0, but linearity would require
--   χ(a+b) = χ(a) + χ(b) = 1 + 1 = 0.  Consistent in this case.
-- If a+b ∈ {a,b} (e.g., a+b = a implies b = 0), then χ(a+b) = 1
-- but linearity gives 0.  Inconsistent.
--
-- So the pair is NOT defined by a linear predicate on the population.
-- Instead, the pair is defined by the ANNIHILATOR condition:
--   {a,b} is a κ-equivalence class iff a+b ∈ κ⊥
--   i.e., d · (a+b) = 0 for all d ∈ κ.
-- This means: no discriminator in κ can tell a from b.
-- The pair is defined by what κ CANNOT distinguish.

-- Proof: d · (a+b) = d · a + d · b (bilinearity).
-- If d · a = d · b for all d ∈ κ, then d · (a+b) = d·a + d·a = 0
-- (by double-cancel).

-- The annihilator condition via bilinearity:
pairing-via-annihilator :
  ∀ {n} (d a b : GF2Vec n)
  → a ·V d ≡ b ·V d
  → (a +V b) ·V d ≡ 𝟘
pairing-via-annihilator {n} d a b eq = begin
  (a +V b) ·V d            ≡⟨ ·V-linearˡ a b d ⟩
  (a ·V d) +F (b ·V d)     ≡⟨ cong ((a ·V d) +F_) (sym eq) ⟩
  (a ·V d) +F (a ·V d)     ≡⟨ double-cancel (a ·V d) ⟩
  𝟘                         ∎
  where open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
        open ≡-Reasoning
