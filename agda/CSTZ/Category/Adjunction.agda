------------------------------------------------------------------------
-- CSTZ.Category.Adjunction
--
-- Paper §6, Thm 6.11: Triadic adjunction system.  [Axiom class A]
--
-- "S₃ symmetry of the triangle identity generates 6 adjunctions —
-- 3 chirality pairs — by permuting {κ,σ,τ} over the adjunction
-- stencil A ← B → C."
------------------------------------------------------------------------

module CSTZ.Category.Adjunction where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

-- The triangle identity κ = σ + τ (over GF(2)) has S₃ = Sym(3)
-- symmetry acting by permutation of the three vertices.
-- Each of the 6 permutations gives an adjunction:
--
--   1. κ-axis:  Free ⊣ Forgetful  (inclusion ⊣ projection)
--   2. σ-axis:  σ-Free ⊣ σ-Forgetful
--   3. τ-axis:  τ-Free ⊣ τ-Forgetful
--   4-6. The three chirality-reversed versions.
--
-- Each is a retract adjunction (zig-zag equations trivially
-- satisfied because the morphisms are projections/inclusions
-- between direct summands over GF(2)).

-- Number of triadic adjunctions
triadic-adjunction-count : ℕ
triadic-adjunction-count = 6

-- The full verification of zig-zag equations for each adjunction
-- is in Verification modules (App B.1).
