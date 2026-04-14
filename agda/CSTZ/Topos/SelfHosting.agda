------------------------------------------------------------------------
-- CSTZ.Topos.SelfHosting
-- Paper §9, Thm 9.14: Self-hosting.  [AP]
-- Boolean restriction of Ω reconstructs GF(2) internally:
-- GF(2)_ext → four-valued logic → Boolean type → GF(2)_int
------------------------------------------------------------------------
module CSTZ.Topos.SelfHosting where

open import CSTZ.GF2
open import CSTZ.Topos.SubobjClassifier

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- The Boolean restriction of Ω = {(1,0), (0,1)} under the map
-- (1,0) ↦ true, (0,1) ↦ false IS GF(2):
--   "addition" = swap-then-project = xor
--   "multiplication" = componentwise ∧ then project = ∧

-- Projection from Boolean Ω values to GF(2)
-- (1,0) ↦ true;  (0,1) ↦ false
boolProject : Ω → F
boolProject (true  , false) = 𝟙
boolProject (false , true)  = 𝟘
boolProject _               = 𝟘  -- gap/overlap: degenerate

-- Self-hosting check: boolProject ∘ ¬Ω = not
self-host-neg : boolProject (¬Ω ⊤Ω) ≡ 𝟘
self-host-neg = refl

self-host-neg2 : boolProject (¬Ω ⊥Ω) ≡ 𝟙
self-host-neg2 = refl
