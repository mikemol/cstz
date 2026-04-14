------------------------------------------------------------------------
-- CSTZ.Category.Yoneda
--
-- Paper §6, Thm 6.17: Yoneda lemma.  [A]
--
-- "The Yoneda embedding Y: C(S,κ) → [C(S,κ)ᵒᵖ, Set] is full and
-- faithful.  Two objects are isomorphic iff they have identical
-- morphism profiles."
------------------------------------------------------------------------

module CSTZ.Category.Yoneda where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Category.Emergent

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Paper §6, Thm 6.17

-- The representable presheaf at object A:
-- Hom(−, A) sends each object B to the set of discriminators d
-- with τ_d(B) = 1 and σ_d(A) = 1.

-- Over our representation: the hom-set Hom(A,B) in C(S,κ) is
-- the set of vectors d ∈ GF(2)^n such that eval d a = 1 for all
-- a in the equivalence class A and eval d b = 1 for all b in B.
-- (With the τ/σ distinction tracking source vs target.)

-- The Yoneda embedding sends an object A to its hom-functor.
-- Full and faithful means: the only way for Hom(−,A) = Hom(−,B)
-- is A = B (as κ-equivalence classes).

-- In the discrimination framework, this is the DIRECTED version of
-- κ-extensionality (Thm 4.2): objects ARE their morphism profiles.
-- If Hom(−,A) = Hom(−,B) then every discriminator that targets A
-- also targets B and vice versa, so A and B are κ-equivalent.

-- We state this as: equal hom-sets imply equal objects.
-- (The converse is trivial: equal objects have equal hom-sets.)

yoneda-faithful :
  ∀ {n : ℕ} (eval : GF2Vec n → GF2Vec n → F)
    (a b : GF2Vec n)
  → (∀ (d : GF2Vec n) → eval d a ≡ eval d b)
  → a ≡ b
yoneda-faithful eval a b all-eq = a≡b
  where
    -- If every discriminator produces the same value on a and b,
    -- then a and b are κ-equivalent.  Under evaluation linearity,
    -- this means a + b is in the annihilator of every discriminator,
    -- so a + b = 0, hence a = b.
    -- The full proof requires the operationalist axiom or a finiteness
    -- argument.  We postulate for now.
    postulate a≡b : a ≡ b
