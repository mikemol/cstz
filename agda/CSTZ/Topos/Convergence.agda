------------------------------------------------------------------------
-- CSTZ.Topos.Convergence
--
-- Paper §9, Thm 9.22: Convergence rate = 3.  [Axiom class A]
--
-- "Three linearly independent interrogations per dimension suffice
-- to determine all seven Fano points."
------------------------------------------------------------------------

module CSTZ.Topos.Convergence where

open import Data.Nat using (ℕ)

-- The convergence rate is 3 = dim(GF(2)³).
-- Three non-collinear points determine all 7 via Fano inference.
-- The minimum generating set for GL(3,GF(2)) acting on the Fano
-- plane has size 3.  After 3 interrogations, the Galois group is
-- trivial: Gal(V/κ) reduces from GL(3,GF(2)) ≅ PSL(2,7) (order
-- 168) to the trivial group.

convergence-rate : ℕ
convergence-rate = 3

-- Galois group order at each stage:
-- κ₀ = ∅: |GL(3,GF(2))| = 168
-- κ₁ = ⟨e₁⟩: |stabilizer| = 168/7 * ... = 24 → actually 6
-- κ₂ = ⟨e₁,e₂⟩: |GL(1,GF(2))| = 1
-- κ₃ = V: trivial
