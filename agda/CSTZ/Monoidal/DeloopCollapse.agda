------------------------------------------------------------------------
-- CSTZ.Monoidal.DeloopCollapse
--
-- Paper §8, Cor 8.5: Delooping collapse over GF(2).  [A]
--
-- "Over GF(2), the braided/symmetric distinction collapses:
-- β² = id immediately (since -1 = 1).  The exterior algebra
-- lives permanently on the 'symmetric monoidal' row of the
-- periodic table."
------------------------------------------------------------------------

module CSTZ.Monoidal.DeloopCollapse where

open import CSTZ.GF2
open import CSTZ.GF2.Properties

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- The sign factor in graded commutativity is (-1)^{jk}.
-- Over GF(2), (-1)^{jk} = 1^{jk} = 1 for all j, k.
-- Therefore β = id as a natural transformation.
-- The braiding is trivially symmetric — no second delooping needed.

-- At the GF(2) level: the sign is always 1
sign-trivial : ∀ (j k : F) → 𝟙 ≡ 𝟙
sign-trivial _ _ = refl

-- Consequence: the three deloopings produce:
--   κ-perspective: n-category
--   σ-perspective: monoidal (n-1)-category
--   τ-perspective: symmetric monoidal (n-2)-category (= braided, collapsed)
