------------------------------------------------------------------------
-- CSTZ.Framework.WriteRead
--
-- Paper §3: Write path vs read path distinction.
--
-- Write path (κ-evolution): linear, each residue consumed once.
-- Read path (evaluation): monoidal, freely iterable.
--
-- Paper §3, Prop 3.8: "Order-independence of filtration: the
-- profile vector is independent of evaluation order."
------------------------------------------------------------------------

module CSTZ.Framework.WriteRead where

-- The write/read distinction is primarily a conceptual framework
-- rather than a type-level enforcement in this formalization.
--
-- Write path = κ-evolution (adding discriminators, consuming residues)
--   → Defined in CSTZ.Framework.Regime.evolve
--   → Linear: each residue is consumed exactly once
--
-- Read path = evaluation over a fixed κ
--   → Defined in CSTZ.Framework.Discriminator.eval
--   → Monoidal: freely iterable, order-independent
--
-- The order-independence property (Prop 3.8) states that
-- evaluating discriminators d₁,...,dₙ on element a produces
-- the same profile vector regardless of evaluation order.
-- Over GF(2), this follows from commutativity of xor.

-- For now, this module serves as documentation.  The property
-- is used implicitly wherever we evaluate multiple discriminators
-- and assume the result is well-defined (i.e., independent of
-- evaluation order).
