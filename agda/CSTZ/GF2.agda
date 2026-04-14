------------------------------------------------------------------------
-- CSTZ.GF2
--
-- The two-element field GF(2), represented as Bool with xor as
-- addition and ∧ as multiplication.
--
-- Paper §2: "GF(2) is the field {0,1} with characteristic 2,
-- where 1+1=0 and every element is its own additive inverse."
------------------------------------------------------------------------

module CSTZ.GF2 where

open import Data.Bool.Base public
  using ( Bool ; true ; false
        ; _xor_ ; _∧_ ; not
        ; if_then_else_
        )

-- GF(2) vocabulary aliases.  The paper uses additive/multiplicative
-- notation throughout; these make Agda code read like the paper.

F : Set
F = Bool

-- Additive identity (zero element)
𝟘 : F
𝟘 = false

-- Multiplicative identity (one element)
𝟙 : F
𝟙 = true

-- Addition in GF(2) = xor
_+F_ : F → F → F
_+F_ = _xor_

-- Multiplication in GF(2) = and
_·F_ : F → F → F
_·F_ = _∧_

-- Additive inverse: every element is its own inverse over GF(2)
-F_ : F → F
-F x = x    -- since x + x = 0

infixl 6 _+F_
infixl 7 _·F_
infix  8 -F_
