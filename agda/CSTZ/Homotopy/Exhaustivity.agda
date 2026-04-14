------------------------------------------------------------------------
-- CSTZ.Homotopy.Exhaustivity
--
-- Paper §5, Thm 5.7: Exhaustivity is operational.  [Axiom class A]
--
-- "∂ ∘ ∂ = 0 entails that every residue fully specifies its own
-- shape.  The homology class of a residue constitutes a complete
-- description of the discriminator required to consume it."
--
-- Constructive filling: C = R ∧ e_{n+1}, then ∂C = R.
------------------------------------------------------------------------

module CSTZ.Homotopy.Exhaustivity where

open import CSTZ.GF2
open import CSTZ.Exterior.Basis
open import CSTZ.Exterior.Boundary

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Paper §5, Thm 5.7:
--
-- Given a residue R (a cycle in ker ∂ₖ that is not in im ∂ₖ₊₁),
-- the filling C = R ∧ e_{n+1} satisfies ∂C = R by the Leibniz rule:
--   ∂(R ∧ e_{n+1}) = (∂R) ∧ e_{n+1} + R · ∂(e_{n+1})
--                   = 0 · e_{n+1} + R · 1    (since ∂R = 0, ∂(eᵢ) = 1)
--                   = R
--
-- κ-evolution itself IS the constructive filling procedure.

-- The Leibniz rule for ∂ on a wedge product:
-- ∂(a ∧ b) = (∂a) ∧ b + a · (∂b)    (graded Leibniz rule)
--
-- Over GF(2), signs don't matter, so this is literally additive.
-- The full proof requires relating our ∂ (defined via position
-- removal) to the wedge product structure.

postulate
  -- Leibniz rule: ∂ distributes over ∧ (graded product rule)
  leibniz : ∀ {n} (a b : Exterior n) (t : Subset n)
    → ∂ (λ s → a s ·F b s) t ≡ 𝟘  -- Placeholder type; needs wedge-∂ interaction

  -- Exhaustivity: for any cycle R (with ∂R = 0), there exists a
  -- filling C such that ∂C = R, constructible as R ∧ e_{n+1}.
  -- The full statement requires the wedge product on Exterior elements,
  -- which needs the sum-over-decompositions form.
  exhaustive-filling : ∀ {n} (R : Exterior n) (t : Subset n)
    → ∂ R t ≡ 𝟘  -- R is a cycle
    → Subset (suc n)  -- the filling C lives in the extended space
-- Paper: "Each residue arrives with the specification of the
-- discriminator needed to consume it."
