------------------------------------------------------------------------
-- CSTZ.Higher.N1Category
--
-- Paper §7, Thm 7.1: Natural (n,1)-structure.  [Axiom class A]
--
-- "C(S,κ) is an (n,1)-category: 1-morphisms directed, k-morphisms
-- for k≥2 symmetric and invertible.  This follows from the
-- architecture: ∧ is commutative over GF(2), so higher morphisms
-- are self-inverse.  Direction requires τ/σ asymmetry, which
-- only the population interface provides — at grade 1."
------------------------------------------------------------------------

module CSTZ.Higher.N1Category where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Exterior.Wedge

-- Paper §7, Thm 7.1:
-- Grade 1: directed (τ/σ labels discriminate source from target).
-- Grade k ≥ 2: symmetric (∧ commutative → every k-morphism equals
--   its own reversal: d_k ∧ ⋯ ∧ d_1 = d_1 ∧ ⋯ ∧ d_k).
-- Every k-morphism is self-inverse (−x = x over GF(2)).
--
-- This is not a design choice — it follows from char(GF(2)) = 2.

-- The commutativity that kills direction at grade ≥ 2:
-- wedge₂-comm from Exterior.Wedge already proves this.
