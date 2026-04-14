------------------------------------------------------------------------
-- CSTZ.Monoidal.CayleyDickson
--
-- Paper §8, Def 8.8: Cayley-Dickson tower over GF(2)².  [A]
--
-- Step 0: GF(2) — scalars (symmetric monoidal)
-- Step 1: GF(2)² with swap conjugation (symmetric monoidal)
-- Step 2: GF(2)⁴ — non-commutative (braided monoidal)
-- Step 3: GF(2)⁸ — non-associative (merely monoidal)
------------------------------------------------------------------------

module CSTZ.Monoidal.CayleyDickson where

open import CSTZ.GF2
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

-- Paper §8, Def 8.7: Swap conjugation on GF(2)²
-- (a, b)* = (b, a)
-- This is ¬ on Ω: it swaps τ and σ components.
swap : F × F → F × F
swap (a , b) = (b , a)

-- Cayley-Dickson multiplication at step 1:
-- (a, b)(c, d) = (ac + d*b, da + bc*)
-- Over GF(2), conjugation a* = a (since -1 = 1 makes (a*, -b) = (a, b)).
-- So: (a,b)(c,d) = (ac + db, da + bc) = (ac xor db, da xor bc)

cd-mul : (F × F) → (F × F) → (F × F)
cd-mul (a , b) (c , d) =
  ((a ·F c) +F (d ·F b) , (d ·F a) +F (b ·F c))

-- Zero divisors: (1,0) · (0,1) = (0·0 + 1·1, 1·1 + 0·0) = (1, 1)
-- Wait: let me compute: a=1,b=0,c=0,d=1:
--   ((1·0)+(1·0), (1·1)+(0·0)) = (0+0, 1+0) = (0, 1)
-- Actually: (1,0)·(0,1) = (1·0 xor 1·0, 1·1 xor 0·0) = (0, 1)
-- And (0,1)·(1,0) = (0·1 xor 0·0, 0·0 xor 1·1) = (0, 1)
-- These are equal, so step 1 IS commutative.
-- The non-commutativity arises at step 2 (GF(2)⁴).
-- See Verification.CDHexagon (App B.39) for the recognizer-based resolution.
