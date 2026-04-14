------------------------------------------------------------------------
-- CSTZ.Topos.Irremovable
--
-- Paper §9, Thm 9.16: Discrimination is irremovable.  [AP]
--
-- Removing discrimination produces four independent failures
-- (sheaf, manifold, bimodule, self-resolution) and a homological
-- gap whose specified filling is discrimination.
------------------------------------------------------------------------

module CSTZ.Topos.Irremovable where

open import CSTZ.GF2
open import CSTZ.Exterior.Basis
open import CSTZ.Topos.FixedPoint

open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Paper §9, Thm 9.16

-- The four independent failures upon removing discrimination:
data RemovalFailure : Set where
  sheaf-failure      : RemovalFailure  -- gluing condition breaks
  manifold-failure   : RemovalFailure  -- local charts lose transition
  bimodule-failure   : RemovalFailure  -- left/right module structure breaks
  self-resolution-failure : RemovalFailure  -- framework can't describe itself

-- The homological argument:
-- Removing the unique grade-2 element e₁ ∧ e₂ from Λ(GF(2)²)
-- creates a gap in H₂.  By exhaustivity (Thm 5.7), this gap
-- specifies its own filling: the filling IS e₁ ∧ e₂ (discrimination).
-- Removal reinstates what it removed.

-- This is INTERNAL necessity: it uses the framework's own
-- gap-filling machinery.  A reader who has not accepted the
-- framework has no reason to accept this argument.  The
-- circularity is acknowledged (Paper §9, Thm 9.16 footnote).

-- The key fact that makes this work is unique-top-form from
-- FixedPoint: there is exactly ONE non-zero grade-2 element,
-- so the filling is uniquely determined.
