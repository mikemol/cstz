------------------------------------------------------------------------
-- CSTZ.Category.Yoneda
--
-- Paper §6, Thm 6.17: Yoneda lemma.  [Axiom class A]
--
-- "The Yoneda embedding Y: C(S,κ) → [C(S,κ)ᵒᵖ, Set] is full and
-- faithful.  Two objects are isomorphic iff they have identical
-- morphism profiles — the directed version of κ-extensionality."
------------------------------------------------------------------------

module CSTZ.Category.Yoneda where

-- Paper §6, Thm 6.17:
-- The Yoneda lemma is the directed version of extensionality:
-- an object's identity is its relational profile (morphism profile).
--
-- In the discrimination framework, this is tautological:
-- objects ARE κ-equivalence classes, defined by their discriminator
-- profiles.  The Yoneda embedding maps each object to its
-- representable presheaf Hom(−, A), and this mapping is injective
-- (full and faithful) because κ-equivalence classes are determined
-- by the morphisms into them.
--
-- The infinite-case resolution (G7) uses the Galois structure:
-- finite Yoneda at each κ, with Galois-equivariant transition
-- maps forming a pro-system.
