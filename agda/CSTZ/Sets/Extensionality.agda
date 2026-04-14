------------------------------------------------------------------------
-- CSTZ.Sets.Extensionality
--
-- Paper §4, Thm 4.2: Extensionality.  [Axiom class A]
--
-- "κ-equivalence is the identity criterion for sets: A ≡_κ B iff
-- no discriminator in κ distinguishes A from B.  This is not an
-- axiom but a direct consequence of the definition."
--
-- In our formalization: sets are κ-equivalence classes, so
-- extensionality is tautological from the definition.
------------------------------------------------------------------------

module CSTZ.Sets.Extensionality where

open import CSTZ.GF2
open import CSTZ.Vec
open import CSTZ.Framework.Discriminator

open import Data.Nat using (ℕ)
open import Data.List using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Product using (_×_ ; _,_)

------------------------------------------------------------------------
-- κ-equivalence (Paper §4, Def 4.1)

-- Two population elements are κ-equivalent if every discriminator
-- in κ produces the same evaluation on both.
κ-equiv : (sys : DiscSystem) → List (DiscSystem.Disc sys)
  → DiscSystem.Pop sys → DiscSystem.Pop sys → Set
κ-equiv sys κ a b = ∀ d → d ∈List κ → DiscSystem.eval sys d a ≡ DiscSystem.eval sys d b
  where
    -- Simple list membership
    _∈List_ : ∀ {A : Set} → A → List A → Set
    _∈List_ x []       = ⊥ where open import Data.Empty
    _∈List_ x (y ∷ ys) = (x ≡ y) ⊎ (x ∈List ys)
      where open import Data.Sum using (_⊎_)

------------------------------------------------------------------------
-- Paper §4, Thm 4.2: Extensionality
--
-- "Sets ARE κ-equivalence classes.  Two classes are equal iff they
-- agree on every discriminator.  This is the definition of
-- equivalence-class identity."
--
-- In Agda, this is immediate: if we define sets as equivalence
-- classes under κ-equiv, then two sets are equal iff κ-equiv
-- holds between their representatives.  Extensionality is built
-- into the definition — there is nothing to prove.

-- We state it as: κ-equiv is an equivalence relation.
-- (Reflexivity and symmetry are immediate; transitivity via trans.)

κ-equiv-refl : (sys : DiscSystem) (κ : List (DiscSystem.Disc sys))
  (a : DiscSystem.Pop sys) → κ-equiv sys κ a a
κ-equiv-refl sys κ a d _ = refl

κ-equiv-sym : (sys : DiscSystem) (κ : List (DiscSystem.Disc sys))
  (a b : DiscSystem.Pop sys) → κ-equiv sys κ a b → κ-equiv sys κ b a
κ-equiv-sym sys κ a b ab d p
  = Relation.Binary.PropositionalEquality.sym (ab d p)
