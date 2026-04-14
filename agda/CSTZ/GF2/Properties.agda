------------------------------------------------------------------------
-- CSTZ.GF2.Properties
--
-- Properties of GF(2) = (Bool, xor, ∧).
--
-- The single most important lemma is `double-cancel`:
--   ∀ b → b xor b ≡ false
--
-- This fact (1+1=0 in characteristic 2) drives ∂∘∂=0, Russell
-- exclusion, the interchange law, groupoid symmetry, and the
-- braided/symmetric collapse.  Half the paper's proofs reduce to it.
--
-- Paper §2: "Over GF(2), 1+1=0 and every element is its own
-- additive inverse, so there is no distinct negation."
------------------------------------------------------------------------

module CSTZ.GF2.Properties where

open import CSTZ.GF2
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open ≡-Reasoning

-- Re-export the stdlib proofs under paper-aligned names.
open import Data.Bool.Properties public
  using ()
  renaming
    ( xor-same      to double-cancel   -- ∀ b → b xor b ≡ false
    ; xor-assoc     to +F-assoc        -- associativity of addition
    ; xor-comm      to +F-comm         -- commutativity of addition
    ; xor-identityˡ to +F-identityˡ    -- false xor b ≡ b
    ; xor-identityʳ to +F-identityʳ    -- b xor false ≡ b
    ; ∧-assoc       to ·F-assoc        -- associativity of multiplication
    ; ∧-comm        to ·F-comm         -- commutativity of multiplication
    ; ∧-identityˡ   to ·F-identityˡ    -- true ∧ b ≡ b
    ; ∧-identityʳ   to ·F-identityʳ    -- b ∧ true ≡ b
    ; ∧-zeroˡ       to ·F-zeroˡ        -- false ∧ b ≡ false
    ; ∧-zeroʳ       to ·F-zeroʳ        -- b ∧ false ≡ false
    ; ∧-distribˡ-xor to ·F-distribˡ-+F -- a ∧ (b xor c) ≡ (a ∧ b) xor (a ∧ c)
    ; ∧-distribʳ-xor to ·F-distribʳ-+F -- (a xor b) ∧ c ≡ (a ∧ c) xor (b ∧ c)
    ; xor-∧-commutativeRing to GF2-commutativeRing
    )

------------------------------------------------------------------------
-- Derived properties specific to the paper's needs

-- Paper §2: "every element is its own additive inverse"
-- Equivalently: -x = x, since x + x = 0.
self-inverse : ∀ (x : F) → x +F x ≡ 𝟘
self-inverse = double-cancel

-- No distinct negation: not x ≡ x xor true ≡ 1 + x,
-- which is the additive translate, NOT the additive inverse.
-- The additive inverse of x is x itself.
-- This distinguishes GF(2) from Boolean algebra where ¬ is complement.

-- Characteristic 2: 1 + 1 = 0
char2 : 𝟙 +F 𝟙 ≡ 𝟘
char2 = refl

-- Zero annihilates: 0 + x = x  (additive identity)
+F-identity-𝟘ˡ : ∀ x → 𝟘 +F x ≡ x
+F-identity-𝟘ˡ = +F-identityˡ

-- Cancellation: if a + b = 0 then a = b
-- (over GF(2), a + b = 0 iff a = b)
+F-cancel : ∀ {a b : F} → a +F b ≡ 𝟘 → a ≡ b
+F-cancel {false} {false} _ = refl
+F-cancel {false} {true}  ()
+F-cancel {true}  {false} ()
+F-cancel {true}  {true}  _ = refl

-- Converse: a = b implies a + b = 0
+F-cancel⁻ : ∀ {a b : F} → a ≡ b → a +F b ≡ 𝟘
+F-cancel⁻ {false} refl = refl
+F-cancel⁻ {true}  refl = refl

-- Idempotence of multiplication: x · x = x  (since x ∈ {0,1})
·F-idem : ∀ (x : F) → x ·F x ≡ x
·F-idem false = refl
·F-idem true  = refl
