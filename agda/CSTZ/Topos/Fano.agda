------------------------------------------------------------------------
-- CSTZ.Topos.Fano
--
-- Paper §9, Thm 9.20: Fano closure.  [Axiom class A]
--
-- "The seven non-zero points of GF(2)³ form the Fano plane
-- PG(2, GF(2)).  Each line is an instance of the triangle identity
-- p₃ = p₁ + p₂."
------------------------------------------------------------------------

module CSTZ.Topos.Fano where

open import CSTZ.GF2
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- The seven non-zero points of GF(2)³
-- Using (a,b,c) notation for the three components.

p₁ : Vec F 3   -- (1,0,0)
p₁ = true ∷ false ∷ false ∷ []

p₂ : Vec F 3   -- (0,1,0)
p₂ = false ∷ true ∷ false ∷ []

p₃ : Vec F 3   -- (0,0,1)
p₃ = false ∷ false ∷ true ∷ []

p₄ : Vec F 3   -- (1,1,0)
p₄ = true ∷ true ∷ false ∷ []

p₅ : Vec F 3   -- (1,0,1)
p₅ = true ∷ false ∷ true ∷ []

p₆ : Vec F 3   -- (0,1,1)
p₆ = false ∷ true ∷ true ∷ []

p₇ : Vec F 3   -- (1,1,1)
p₇ = true ∷ true ∷ true ∷ []

-- The 7 Fano lines: each satisfies p_a + p_b = p_c
-- (where + is pointwise xor)

open import CSTZ.Vec using (_+V_)

-- Line 1: p₁ + p₂ = p₄  i.e. (1,0,0) + (0,1,0) = (1,1,0)
fano-line-1 : p₁ +V p₂ ≡ p₄
fano-line-1 = refl

-- Line 2: p₁ + p₃ = p₅  i.e. (1,0,0) + (0,0,1) = (1,0,1)
fano-line-2 : p₁ +V p₃ ≡ p₅
fano-line-2 = refl

-- Line 3: p₂ + p₃ = p₆  i.e. (0,1,0) + (0,0,1) = (0,1,1)
fano-line-3 : p₂ +V p₃ ≡ p₆
fano-line-3 = refl

-- Line 4: p₁ + p₆ = p₇  i.e. (1,0,0) + (0,1,1) = (1,1,1)
fano-line-4 : p₁ +V p₆ ≡ p₇
fano-line-4 = refl

-- Line 5: p₂ + p₅ = p₇  i.e. (0,1,0) + (1,0,1) = (1,1,1)
fano-line-5 : p₂ +V p₅ ≡ p₇
fano-line-5 = refl

-- Line 6: p₃ + p₄ = p₇  i.e. (0,0,1) + (1,1,0) = (1,1,1)
fano-line-6 : p₃ +V p₄ ≡ p₇
fano-line-6 = refl

-- Line 7: p₄ + p₅ = p₆ is wrong; let me check...
-- Actually: p₄ + p₆ = (1,1,0)+(0,1,1) = (1,0,1) = p₅
fano-line-7 : p₄ +V p₆ ≡ p₅
fano-line-7 = refl

-- All 7 lines verified by refl (computation)!
-- Paper: "If two points on a Fano line have γ=1, the third is
-- determined by inference."
