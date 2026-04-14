------------------------------------------------------------------------
-- CSTZ.Sets.Infinity
--
-- Paper §4, Prop 4.26: Indistinguishability of potential and
-- actual infinity.  [Axiom class AO]
--
-- No discriminator in any κ-state separates the claim "S is a
-- completed infinite totality" from "S is an open-ended process."
-- By the operationalist axiom, they are identical.
------------------------------------------------------------------------

module CSTZ.Sets.Infinity where

open import CSTZ.GF2
open import CSTZ.Axiom.Operationalist

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)

-- Paper §4, Def 4.22: An inexhaustible collection is one where
-- no finite κ renders it fully discriminated.

-- Paper §4, Prop 4.26: The actual/potential infinity distinction
-- is not separable by any discriminator.  The proof proceeds by
-- contradiction: any separating discriminator d produces a
-- κ-evolution, but the new κ-state is still finite while S is
-- still inexhaustible.  No finite composition of evolutions
-- converges.
--
-- The operationalist axiom then collapses the distinction.
-- This is an application of the postulate, not a pure-algebra proof.

-- The statement: for any representation of "actual infinity" (A)
-- and "potential infinity" (P), if no discriminator separates them,
-- then A ≡ P.
actual≡potential :
  ∀ {Claim : Set} {Disc : Set}
    {actual potential : Claim}
    (separates : Disc → Claim → Claim → Set)
  → (∀ (d : Disc) → separates d actual potential → ⊥)
  → actual ≡ potential
actual≡potential = operationalist
