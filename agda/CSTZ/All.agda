------------------------------------------------------------------------
-- CSTZ.All
--
-- Master import: type-checking this file verifies the entire
-- formalization compiles.
------------------------------------------------------------------------

module CSTZ.All where

-- Phase 1: Algebra
open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Vec
open import CSTZ.Vec.Properties
open import CSTZ.Exterior

-- Phase 2: Axioms + Framework (§3)
open import CSTZ.Axiom.ProfileLinearity
open import CSTZ.Axiom.EvalLinearity
open import CSTZ.Axiom.Operationalist
open import CSTZ.Framework

-- Phase 3: Sets (§4)
open import CSTZ.Sets

-- Phase 4: Homotopy (§5)
open import CSTZ.Homotopy

-- Phase 5: Categories (§6)
open import CSTZ.Category

-- Phase 6: Higher (§7)
open import CSTZ.Higher

-- Phase 7: Monoidal (§8)
open import CSTZ.Monoidal

-- Phase 8: Topos (§9)
open import CSTZ.Topos

-- Phase 9: Verification (App B gap-closers)
open import CSTZ.Verification.Segal
open import CSTZ.Verification.RISC
open import CSTZ.Verification.CDHexagon
open import CSTZ.Verification.ChoiceBound
open import CSTZ.Verification.PairingBilinear
open import CSTZ.Verification.FixedPointStab
open import CSTZ.Verification.ChainBound
open import CSTZ.Verification.OmegaChain
open import CSTZ.Verification.Annihilator
open import CSTZ.Verification.MonoidalCoherence
open import CSTZ.Verification.LimitsExhaustive
