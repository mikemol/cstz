------------------------------------------------------------------------
-- CSTZ.Category.Limits
--
-- Paper §6, Prop 6.20: Limits from exhaustive filtration.  [A]
--
-- "A missing limit is a residue that specifies its own filling;
-- consuming it via κ-evolution gives the limit in the extended
-- category.  Completeness is not a static property but a dynamic
-- relationship."
------------------------------------------------------------------------

module CSTZ.Category.Limits where

-- Five limit types constructed in the paper:
-- 1. Terminal object: the trivial κ-equivalence class
-- 2. Product: computed at κ₁ ∨ κ₂ (join of stages)
-- 3. Equalizer: kernel of difference morphism
-- 4. Pullback: product + equalizer
-- 5. General finite limit: iterated pullback
--
-- Universality from GF(2)-linearity: factoring morphisms are unique
-- because linear maps are determined by basis values.
--
-- Full exhaustive construction: Verification.LimitsExhaustive (App B.26).
