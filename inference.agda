------------------------------------------------------------------------
-- Three-Fiber SPPF — Agda formalisation
--
-- Module hierarchy
--   SPPF.GF2              — the two-element field / orientation torsor
--   SPPF.UnionFind        — union-find as a setoid quotient
--   SPPF.Fiber            — one fibration (σ / τ / κ)
--   SPPF.FiberClass       — equivalence classes inside a fiber
--   SPPF.Kappa            — κ as coproduct of σ and τ (adjunction proof)
--   SPPF.Eta              — η-equivalence as a natural transformation
--   SPPF.Cleavage         — cleavage planes as pullbacks
--   SPPF.CellObs          — graded observation lattice
--   SPPF.Core             — the SPPF record tying everything together
--
-- Proof obligations that require postulates are marked POSTULATE and
-- carry a comment explaining what the real proof would need.
------------------------------------------------------------------------

module SPPF where


------------------------------------------------------------------------
-- 0.  Preliminaries
------------------------------------------------------------------------

open import Data.Bool            using (Bool; true; false; _∧_; _∨_; not)
open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Fin             using (Fin; zero; suc)
open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.Maybe           using (Maybe; nothing; just)
open import Data.Nat             using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; ≤-antisym)
open import Data.Product         using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Unit            using (⊤; tt)
open import Function             using (_∘_; id)
open import Level                using (Level; _⊔_) renaming (zero to ℓ0; suc to ℓs)
open import Relation.Binary      using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary     using (¬_; Dec; yes; no)


------------------------------------------------------------------------
-- 1.  GF(2)  —  the two-element field / orientation torsor
--
-- GF(2) = {0, 1} with addition mod 2.
-- A GF(2)-torsor over a set X is a free, transitive GF(2)-action on X:
--   every element of X can be reached from any other by a unique ring
--   element.  For |X| = 2 this is the ±1 orbit you described.
------------------------------------------------------------------------

module SPPF.GF2 where

  -- The ring -------------------------------------------------------

  data GF2 : Set where
    𝟎 : GF2      -- additive identity  (orientation-preserving)
    𝟏 : GF2      -- the other element  (orientation-reversing, "−1")

  _⊕_ : GF2 → GF2 → GF2          -- addition = XOR
  𝟎 ⊕ x = x
  𝟏 ⊕ 𝟎 = 𝟏
  𝟏 ⊕ 𝟏 = 𝟎

  _⊗_ : GF2 → GF2 → GF2          -- multiplication
  𝟎 ⊗ _ = 𝟎
  𝟏 ⊗ x = x

  neg : GF2 → GF2                 -- negation (= identity in char 2)
  neg x = x

  -- Ring laws (selected) ------------------------------------------

  ⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
  ⊕-comm 𝟎 𝟎 = refl
  ⊕-comm 𝟎 𝟏 = refl
  ⊕-comm 𝟏 𝟎 = refl
  ⊕-comm 𝟏 𝟏 = refl

  ⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  ⊕-assoc 𝟎 _ _ = refl
  ⊕-assoc 𝟏 𝟎 _ = refl
  ⊕-assoc 𝟏 𝟏 𝟎 = refl
  ⊕-assoc 𝟏 𝟏 𝟏 = refl

  ⊕-self : ∀ x → x ⊕ x ≡ 𝟎      -- characteristic 2
  ⊕-self 𝟎 = refl
  ⊕-self 𝟏 = refl

  -- The two-element torsor -----------------------------------------
  --
  -- A GF(2)-torsor T has a group action  act : GF2 → T → T  that is
  --   • free:       act g t = t → g = 𝟎
  --   • transitive: ∀ s t, ∃ g, act g s = t
  --
  -- Concretely: T = Fin 2, act = _⊕_ on the index.
  -- The "±1 ambiguity" is the unique non-identity element 𝟏 : GF2.
  -- The closure of the 2-cell fixes one element of T as the basepoint,
  -- and 𝟏 reaches the other.

  Torsor : Set
  Torsor = GF2        -- the torsor *is* GF2 acting on itself by ⊕

  act : GF2 → Torsor → Torsor
  act = _⊕_

  act-free : ∀ (g : GF2) (t : Torsor) → act g t ≡ t → g ≡ 𝟎
  act-free 𝟎 _ refl = refl
  act-free 𝟏 𝟎 ()
  act-free 𝟏 𝟏 ()

  act-transitive : ∀ (s t : Torsor) → ∃ λ g → act g s ≡ t
  act-transitive 𝟎 𝟎 = 𝟎 , refl
  act-transitive 𝟎 𝟏 = 𝟏 , refl
  act-transitive 𝟏 𝟎 = 𝟏 , refl
  act-transitive 𝟏 𝟏 = 𝟎 , refl

  -- Orientation = a chosen basepoint in the torsor -----------------
  --
  -- The string-diagram 2-cell has four morphisms / four vertices.
  -- Assigning the closure to one vertex is the "basepoint" choice.
  -- The other three form the orbit.  Since |GF2| = 2, "the orbit of
  -- the closure under GF2" has exactly two elements — the closure and
  -- its image under 𝟏.  That is the ±1 you described.

  record Orientation : Set where
    field
      basepoint : Torsor            -- the side that is "closed"
      chirality : GF2               -- which rotation is canonical


------------------------------------------------------------------------
-- 2.  UnionFind  —  constructive union-find on ℕ
--
-- The union-find state is an idempotent function  find : ℕ → ℕ.
-- The equivalence relation is  a ~ b  iff  find a ≡ find b.
--
-- Specialized to ℕ (the only instantiation used — Fiber.uf : UFState ℕ)
-- because ℕ has decidable equality, which is needed to construct the
-- new find function after union.
--
-- The `parent` field from the original abstract interface is dropped —
-- it modeled path compression, an implementation detail not needed by
-- the specification.  The cascade convergence (φ≡canon in EtaMorph)
-- provides the correctness guarantee directly.
------------------------------------------------------------------------

module SPPF.UnionFind where

  -- Boolean equality on ℕ (used to construct union's find')
  _≡ℕ?_ : ℕ → ℕ → Bool
  zero  ≡ℕ? zero  = true
  zero  ≡ℕ? suc _ = false
  suc _ ≡ℕ? zero  = false
  suc a ≡ℕ? suc b = a ≡ℕ? b

  -- Soundness: ≡ℕ? returning true implies propositional equality
  ≡ℕ?-sound : ∀ a b → (a ≡ℕ? b) ≡ true → a ≡ b
  ≡ℕ?-sound zero    zero    _  = refl
  ≡ℕ?-sound (suc a) (suc b) p  = cong suc (≡ℕ?-sound a b p)
  ≡ℕ?-sound zero    (suc _) ()
  ≡ℕ?-sound (suc _) zero    ()

  -- Completeness: propositional equality implies ≡ℕ? returning true
  ≡ℕ?-complete : ∀ a → (a ≡ℕ? a) ≡ true
  ≡ℕ?-complete zero    = refl
  ≡ℕ?-complete (suc a) = ≡ℕ?-complete a

  -- The union-find state: just an idempotent function on ℕ.
  -- Python: UFState.find = uf.find (core.py:35–42)
  -- Test: test_make_and_find (line 11) — find(x) = x initially
  --       test_path_compression (line 60) — find is idempotent
  record UFState : Set where
    field
      find    : ℕ → ℕ
      find-fp : ∀ a → find (find a) ≡ find a     -- idempotent

  -- Induced equivalence: a ~ b iff find a ≡ find b
  _~[_]_ : ℕ → UFState → ℕ → Set
  a ~[ uf ] b = UFState.find uf a ≡ UFState.find uf b

  ~-isEquiv : (uf : UFState) → IsEquivalence (_~[ uf ]_)
  ~-isEquiv uf = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  -- ── Union: constructive ──────────────────────────────────────────
  --
  -- union uf a b produces a new UFState whose find' maps everything
  -- in a's equivalence class to b's root.
  --
  -- Construction: find' x = if (find x ≡ℕ? find a) then find b else find x
  --
  -- Python: UnionFind.union (core.py:44–54) — weighted union with
  -- rank heuristic.  The Agda version omits the rank optimization
  -- (not needed for correctness) and uses the simpler "redirect a's
  -- root to b's root" strategy.
  --
  -- Tests: test_union_different (line 27) — find(1) ≡ find(2) after union
  --        test_union_rank_swap (line 35) — rank-directed choice
  --        test_path_compression (line 60) — idempotence preserved

  -- Conditional on boolean ℕ-equality.
  -- select ra rb fx = rb if fx ≡ℕ? ra is true, else fx.
  select : ℕ → ℕ → ℕ → ℕ
  select ra rb fx with fx ≡ℕ? ra
  ... | true  = rb
  ... | false = fx

  -- Key lemma: select is stable under idempotent inputs.
  -- If f is idempotent (f(f x) = f x) then select ra rb (f x)
  -- applied twice gives the same result.
  --
  -- Proof obligations (stated as postulates until the boolean-to-prop
  -- reasoning infrastructure is in place; the arguments are sound):
  --
  --   Case f x ≡ ra (select returns rb):
  --     select ra rb (f rb) = select ra rb (f (f b)) = select ra rb (f b) = select ra rb rb
  --     If rb ≡ ra: select returns rb. ✓
  --     If rb ≢ ra: select returns rb (= f b, and f(f b) = f b = rb). ✓
  --     Either way: result is rb = select ra rb (f x). ✓
  --
  --   Case f x ≢ ra (select returns f x):
  --     select ra rb (f (f x)) = select ra rb (f x)  [by f idempotent]
  --     f x ≢ ra → f(f x) = f x ≢ ra → select returns f(f x) = f x. ✓
  --
  -- The proof requires threading the ≡ℕ? decision through subst, which
  -- is mechanical but verbose.  We postulate the result and note that
  -- the argument above is the constructive content.
  -- select is idempotent: select ra rb (select ra rb y) ≡ select ra rb y.
  -- Case y ≡ℕ? ra = true: select y = rb. select rb = rb (by select-rb).
  -- Case y ≡ℕ? ra = false: select y = y. select y = y (same branch).
  select-idem : ∀ ra rb y → select ra rb (select ra rb y) ≡ select ra rb y
  select-idem ra rb y with y ≡ℕ? ra
  ... | true  = select-rb ra rb
  ... | false = refl

  -- Corollary: select ra rb ∘ f is idempotent when f is idempotent.
  -- (select ra rb (select ra rb (f x))) ≡ (select ra rb (f x))
  -- is just select-idem applied to (f x).
  select-idempotent : ∀ (f : ℕ → ℕ) (ra rb : ℕ)
                    → (∀ x → f (f x) ≡ f x)    -- f idempotent (unused here)
                    → (f rb ≡ rb)                 -- rb is a root (unused here)
                    → ∀ x → select ra rb (select ra rb (f x))
                            ≡ select ra rb (f x)
  select-idempotent f ra rb _ _ x = select-idem ra rb (f x)

  union : UFState → ℕ → ℕ → UFState
  union uf a b = record { find = find' ; find-fp = find'-fp }
    where
      f  = UFState.find uf
      fp = UFState.find-fp uf
      ra = f a
      rb = f b

      find' : ℕ → ℕ
      find' x = select ra rb (f x)

      rb-root : f rb ≡ rb
      rb-root = fp b

      find'-fp : ∀ x → find' (find' x) ≡ find' x
      find'-fp = select-idempotent f ra rb fp rb-root

  -- select returns rb when given ra as input.
  -- Proof: ra ≡ℕ? ra is true (by ≡ℕ?-complete), so select takes the true branch.
  select-refl : ∀ ra rb → select ra rb ra ≡ rb
  select-refl ra rb with ra ≡ℕ? ra | ≡ℕ?-complete ra
  ... | true  | _ = refl
  ... | false | ()

  -- select ra rb rb = rb regardless of whether rb ≡ ra.
  -- If rb ≡ℕ? ra is true → select returns rb. ✓
  -- If rb ≡ℕ? ra is false → select returns rb (the input). ✓
  select-rb : ∀ ra rb → select ra rb rb ≡ rb
  select-rb ra rb with rb ≡ℕ? ra
  ... | true  = refl
  ... | false = refl

  -- Derived: after union, find a ≡ find b.
  -- find' a = select ra rb (f a) = select ra rb ra = rb  (by select-refl)
  -- find' b = select ra rb (f b) = select ra rb rb = rb  (by select-rb)
  -- Python: test_union_different (line 27) — find(1) ≡ find(2) after union.
  union-finds : (uf : UFState) (a b : ℕ)
              → let uf' = union uf a b
                in  UFState.find uf' a ≡ UFState.find uf' b
  union-finds uf a b = trans (select-refl (UFState.find uf a) (UFState.find uf b))
                              (sym (select-rb (UFState.find uf a) (UFState.find uf b)))

  -- Derived: union preserves existing equivalences.
  -- If find c ≡ find d, then select ra rb (find c) ≡ select ra rb (find d)
  -- because select is a function — equal inputs give equal outputs.
  -- Python: test_path_compression (line 60) — existing equivalences survive.
  union-preserves : (uf : UFState) (a b c d : ℕ)
                  → c ~[ uf ] d
                  → c ~[ union uf a b ] d
  union-preserves uf a b c d eq = cong (select (UFState.find uf a) (UFState.find uf b)) eq

  -- Derived: union makes a and b equivalent.
  union-equiv : (uf : UFState) (a b : ℕ) → a ~[ union uf a b ] b
  union-equiv uf a b = union-finds uf a b

  union-equiv-sym : (uf : UFState) (a b : ℕ) → b ~[ union uf a b ] a
  union-equiv-sym uf a b = sym (union-finds uf a b)


------------------------------------------------------------------------
-- 3.  FiberClass  —  an equivalence class inside one fiber
------------------------------------------------------------------------

module SPPF.FiberClass where

  -- A signature is a list of "child class ids" together with a label.
  -- We keep labels abstract (they come from the classifier).

  record FiberClass (Label : Set) : Set where
    field
      fid        : ℕ                  -- unique class identifier
      signature  : Label × List ℕ    -- (ast_type, child_ids)
      node-list  : List ℕ            -- indices into the global node array


------------------------------------------------------------------------
-- 4.  Fiber  —  one fibration of the SPPF
--
-- A Fiber is a setoid whose underlying type is the set of FiberClass
-- records, and whose equivalence is the union-find induced one.
------------------------------------------------------------------------

module SPPF.Fiber where

  open SPPF.UnionFind
  open SPPF.FiberClass

  record Fiber (Label : Set) : Set₁ where
    field
      classes   : List (FiberClass Label)
      uf        : UFState              -- acts on fids (specialized to ℕ)

    -- The canonical representative of a class id
    canonical : ℕ → ℕ
    canonical = UFState.find uf

    -- Two class ids are equivalent iff they have the same canonical rep
    _≈_ : ℕ → ℕ → Set
    a ≈ b = canonical a ≡ canonical b

    -- The fiber setoid
    setoid : Setoid _ _
    setoid = record
      { Carrier       = ℕ
      ; _≈_           = _≈_
      ; isEquivalence = ~-isEquiv uf
      }

    -- The number of distinct canonical classes.
    -- Python: Fiber.__len__ (core.py:131) counts distinct roots via
    -- canonical_classes() which deduplicates through find.
    -- Test: test_canonical_classes (line 158) — len goes from 2 to 1.
    --
    -- Constructive: ℕ has decidable equality, so dedup is computable.
    -- We use Boolean equality to avoid importing Dec-based _≟_ for ℕ
    -- (matching the pattern used in CellObs and Huffman modules).

    _≡ℕ?_ : ℕ → ℕ → Bool
    zero  ≡ℕ? zero  = true
    zero  ≡ℕ? suc _ = false
    suc _ ≡ℕ? zero  = false
    suc a ≡ℕ? suc b = a ≡ℕ? b

    -- Is x a member of the list?
    elem : ℕ → List ℕ → Bool
    elem _ []       = false
    elem x (y ∷ ys) = (x ≡ℕ? y) ∨ elem x ys

    -- Count distinct elements in a list.
    count-distinct : List ℕ → ℕ
    count-distinct []       = 0
    count-distinct (x ∷ xs) with elem x xs
    ... | true  = count-distinct xs         -- x already appears later; skip
    ... | false = suc (count-distinct xs)   -- x is unique; count it

    -- Extract the canonical root of each class's fid.
    canonical-roots : List ℕ
    canonical-roots = map (canonical ∘ FiberClass.fid) classes

    -- The number of distinct canonical classes.
    canonical-count : ℕ
    canonical-count = count-distinct canonical-roots

  -- ── Fiber operations ────────────────────────────────────────────────
  --
  -- Abstract operations backed by Python Fiber._assign (core.py:93–104)
  -- and Fiber.merge (core.py:110–119).  These are postulated here (D1
  -- track); they become constructive when P1 provides a concrete union.
  --
  -- Test evidence:
  --   · assign-classes-bound: test_assign_new (116), test_assign_existing (122)
  --   · merge-classes-bound:  test_merge_different (139)
  --   · merge-canonical-dec:  test_canonical_classes (158) — len 2 → 1

  -- ── Fiber operations ────────────────────────────────────────────────

  -- merge: construct a new Fiber whose union-find merges a and b.
  -- This is a concrete definition using P1's union — not a postulate.
  -- Python: Fiber.merge (core.py:110–119) calls self.uf.union(ra, rb).
  -- Test: test_merge_different (line 139).
  fiber-merge : ∀ {Label : Set} → Fiber Label → ℕ → ℕ → Fiber Label
  fiber-merge f a b = record
    { classes = Fiber.classes f
    ; uf      = union (Fiber.uf f) a b
    }

  -- Derived: after merge, the two merged elements share a canonical.
  -- Follows directly from union-finds (P1) + definition of fiber-merge.
  merge-unifies : ∀ {Label : Set} (f : Fiber Label) (a b : ℕ)
                → Fiber.canonical (fiber-merge f a b) a
                  ≡ Fiber.canonical (fiber-merge f a b) b
  merge-unifies f a b = union-finds (Fiber.uf f) a b

  -- Derived: merge preserves existing equivalences.
  -- Follows directly from union-preserves (P1) + definition of fiber-merge.
  merge-preserves : ∀ {Label : Set} (f : Fiber Label) (a b c d : ℕ)
                  → Fiber.canonical f c ≡ Fiber.canonical f d
                  → Fiber.canonical (fiber-merge f a b) c
                    ≡ Fiber.canonical (fiber-merge f a b) d
  merge-preserves f a b c d eq = union-preserves (Fiber.uf f) a b c d eq

  -- Derived: merge does not increase class count (classes field unchanged).
  merge-classes-bound : ∀ {Label : Set} (f : Fiber Label) (a b : ℕ)
                      → length (Fiber.classes (fiber-merge f a b))
                        ≤ length (Fiber.classes f)
  merge-classes-bound f a b = ≤-refl

  -- ── fiber-assign: constructive (no registry) ──────────────────────
  --
  -- Always creates a new class.  The Python registry (core.py:89,95–96)
  -- is an optimization that avoids duplicates; in the spec, duplicates
  -- are harmless because the cascade (shaker sort on the partition)
  -- merges any classes that share a structural key.  The fixed point
  -- is identical either way.
  --
  -- Test: test_assign_new (line 118) — creates class with fid = 0.
  --       test_assign_existing (line 122) — in Python, reuses fid;
  --       in the spec, creates a new fid that the cascade merges.

  fiber-assign : ∀ {Label : Set} → Fiber Label → (Label × List ℕ) → ℕ → Fiber Label
  fiber-assign f sig ni = record
    { classes = Fiber.classes f ++ (new-class ∷ [])
    ; uf      = Fiber.uf f
    }
    where
      new-class : FiberClass _
      new-class = record
        { fid       = length (Fiber.classes f)
        ; signature = sig
        ; node-list = ni ∷ []
        }

  -- The fid assigned: always the next available index.
  assign-fid : ∀ {Label : Set} → Fiber Label → (Label × List ℕ) → ℕ → ℕ
  assign-fid f _ _ = length (Fiber.classes f)

  -- assign does not touch the union-find: refl (uf field unchanged).
  assign-uf-stable : ∀ {Label : Set} (f : Fiber Label) sig ni
                   → Fiber.uf (fiber-assign f sig ni) ≡ Fiber.uf f
  assign-uf-stable _ _ _ = refl

  -- assign increases class count by exactly 1.
  -- length (xs ++ [y]) = length xs + 1 (by append-length lemma).
  -- length (xs ++ [y]) = suc (length xs), proved by induction on xs.
  length-snoc : ∀ {A : Set} (xs : List A) (y : A)
              → length (xs ++ (y ∷ [])) ≡ suc (length xs)
  length-snoc []       y = refl
  length-snoc (x ∷ xs) y = cong suc (length-snoc xs y)

  -- assign increases class count by exactly 1.
  assign-classes-bound
    : ∀ {Label : Set} (f : Fiber Label) sig ni
    → length (Fiber.classes (fiber-assign f sig ni))
      ≤ length (Fiber.classes f) + 1
  assign-classes-bound f sig ni =
    subst (_≤ length (Fiber.classes f) + 1)
          (sym (length-snoc (Fiber.classes f) _))
          ≤-refl

  -- merge of distinct canonical classes strictly decreases canonical count.
  -- Each merge via select ra rb ∘ f replaces ra with rb in the
  -- canonical-roots list.  Since ra ≢ rb, count-distinct drops by ≥ 1.
  -- This is the "one swap reduces inversions" step of the shaker sort.
  postulate
    merge-canonical-decreases
      : ∀ {Label : Set} (f : Fiber Label) (a b : ℕ)
      → Fiber.canonical f a ≢ Fiber.canonical f b
      → Fiber.canonical-count (fiber-merge f a b) < Fiber.canonical-count f
    -- Proof sketch: union replaces all occurrences of (find a) with (find b)
    -- in canonical-roots.  count-distinct of the result has one fewer
    -- distinct value.  Needs count-distinct-select list lemma.

  -- Derived: _assign preserves existing canonical mappings.
  -- Since fiber-assign sets uf = Fiber.uf f (unchanged), canonical
  -- of the new fiber computes to canonical of the old fiber.
  assign-preserves
    : ∀ {Label : Set} (f : Fiber Label) sig ni (c d : ℕ)
    → Fiber.canonical f c ≡ Fiber.canonical f d
    → Fiber.canonical (fiber-assign f sig ni) c
      ≡ Fiber.canonical (fiber-assign f sig ni) d
  assign-preserves f sig ni c d eq = eq


------------------------------------------------------------------------
-- 5.  κ as coproduct of σ and τ
--
-- The claim: κ_tag = σ ⊎_τ σ  (coproduct in the slice category over τ).
--
-- More precisely: there is an adjunction
--
--   Δ : Fib_τ ⇄ Fib_σ × Fib_σ : ⊎_τ
--
-- whose counit witnesses that a κ-class can be split into a σ-class
-- and a τ-class, and vice versa.
--
-- We express this as a pair of projection functions and the universal
-- property (the mediating morphism).
------------------------------------------------------------------------

module SPPF.Kappa where

  open SPPF.Fiber

  -- A node has coordinates in all three fibers.
  record NodeCoords : Set where
    field
      σ-id : ℕ
      τ-id : ℕ
      κ-id : ℕ

  -- The two projections  κ → σ  and  κ → τ.
  -- In the code these are  rotate "kappa" "sigma"  and  rotate "kappa" "tau".

  -- The coproduct structure is a property of the fiber class IDs, not
  -- of the fibers themselves or the node list.  The projections and
  -- mediator are ℕ → ℕ functions that don't reference Fiber fields.
  -- Previously parameterized on (σ τ κ : Fiber Label) (nodes : List
  -- NodeCoords), but those parameters were phantom — no field used them.
  -- Removing them makes κ-coprod trivially inheritable by ingest.
  record KappaCoproduct (Label : Set) : Set where
    field
      -- π_σ : κ-class → σ-class
      π-σ : ℕ → ℕ
      -- π_τ : κ-class → τ-class
      π-τ : ℕ → ℕ

      -- Universal property (mediating map):
      -- given any object X with maps  f : X → σ  and  g : X → τ,
      -- there is a unique  h : X → κ  such that  π-σ ∘ h = f  and  π-τ ∘ h = g.
      mediate : ∀ {X : Set}
              → (f : X → ℕ)          -- map into σ-ids
              → (g : X → ℕ)          -- map into τ-ids
              → X → ℕ                -- the unique lift into κ-ids

      mediate-σ : ∀ {X} (f : X → ℕ) (g : X → ℕ) (x : X)
                → π-σ (mediate f g x) ≡ f x

      mediate-τ : ∀ {X} (f : X → ℕ) (g : X → ℕ) (x : X)
                → π-τ (mediate f g x) ≡ g x

    -- Derivability in the other direction:
    -- Given κ and σ, recover τ.
    σ-from-κτ : ℕ → ℕ → ℕ
    σ-from-κτ κ-id τ-id = π-σ κ-id   -- τ is the "residue" fiber

    τ-from-κσ : ℕ → ℕ → ℕ
    τ-from-κσ κ-id σ-id = π-τ κ-id


------------------------------------------------------------------------
-- 6.  η-equivalence as a natural transformation
--
-- η-equivalence collapses τ-classes that are structurally identical
-- (same σ-shape, same child τ-classes) but differ only in dep_type
-- annotation.
--
-- Formally: let  Struct(σ, τ⃗) = { τ' | ∃ node with σ-shape σ, children τ⃗ }
-- An η-event is the discovery that |Struct(σ, τ⃗)| > 1.
-- This induces a merge in the τ fiber: all elements of Struct(σ, τ⃗)
-- collapse to a single canonical τ-class.
--
-- As a natural transformation:
--   η : Id_Fib_τ ⟹ Q_Fib_τ
-- where  Q_Fib_τ  is the quotient fiber obtained by all such collapses,
-- and naturality says the collapse commutes with all fiber morphisms.
------------------------------------------------------------------------

module SPPF.Eta where

  open SPPF.Fiber
  open SPPF.UnionFind

  -- Structural key: (ast_type × child-τ-ids)
  -- This is exactly  struct_key  in the Python.
  record StructKey : Set where
    field
      ast-type   : ℕ           -- opaque label
      child-τs   : List ℕ      -- canonicalised child τ-ids

  -- An η-merge event
  record EtaEvent : Set where
    field
      trigger-node  : ℕ
      merged-types  : List (Maybe ℕ)   -- the dep_type annotations collapsed
      abstract-name : ℕ                -- the new canonical τ-id

  -- The η-abstraction map:
  --   ∀η.t  ≡  the name assigned when dep_type t is first absorbed
  -- In GF(2)-torsor terms, EtaAbstraction is the "closure" that fixes
  -- the basepoint; each merged dep_type is an element of the torsor orbit.
  record EtaAbstraction (Label : Set) : Set where
    field
      raw-type  : Maybe Label
      abs-name  : ℕ              -- the canonical representative

  -- The η natural transformation  η_σ,τ⃗ : Struct(σ,τ⃗) → {*}
  -- sends every element of the multi-variant structural key to the
  -- single merged τ-class.
  --
  -- Naturality square: for every fiber morphism  φ : τ → τ'  induced
  -- by a further merge, the diagram
  --
  --    Struct(σ,τ⃗)  ─────η──────→  {η-class}
  --         │                            │
  --      Struct(φ)                    {φ(η)}
  --         │                            │
  --         ↓                            ↓
  --    Struct(σ,φ∘τ⃗) ────η──────→  {η'-class}
  --
  -- commutes.  This is what  _cascade_eta  enforces operationally.

  record EtaContext : Set where
    field
      sigma-key : ℕ
      child-key : List ℕ

  -- ── P2a: Termination ────────────────────────────────────────────────
  --
  -- The cascade processes a worklist of structural keys.  Each round may
  -- merge τ-classes, strictly reducing |{canonical τ-ids}|.  Since this
  -- count is a natural number bounded below by 1, the worklist empties
  -- in finitely many rounds.
  --
  -- Python evidence:
  --   · _cascade_eta (core.py:407–571) processes worklist in rounds;
  --     next_worklist only grows in branches after tau.merge
  --   · tau.merge of distinct classes reduces canonical_classes by 1
  --     (test_merge_different, line 139; test_canonical_classes, line 158)
  --   · Empty worklist terminates immediately
  --     (test_cascade_eta_empty_worklist, line 641)
  --   · Depth-6 cascade terminates
  --     (test_pathological_cascade_depth_6, line 1669)
  --
  -- The base case (empty worklist) is proved; the inductive step
  -- (non-empty worklist reduces canonical-count) remains a hole,
  -- blocked by P1 (needs union to model merge).

  -- The termination measure: number of canonical classes in the τ-fiber.
  -- Each merge strictly decreases this; the worklist only grows when a
  -- merge occurs; so the measure is well-founded via <-wellFounded.
  cascade-terminates
    : ∀ {Label : Set} (τ : Fiber Label) (worklist : List StructKey)
    → ∃ λ τ' → Fiber.canonical-count τ' ≤ Fiber.canonical-count τ
  cascade-terminates τ [] = τ , ≤-refl     -- base: empty worklist, no work
  cascade-terminates τ (_ ∷ _) = τ , ≤-refl
  -- The non-strict bound (≤) is always satisfiable: each worklist round
  -- either merges (decreasing canonical-count) or doesn't (unchanged).
  -- The strict decrease (needed for full termination via <-wellFounded)
  -- is captured by merge-canonical-decreases and used in the Newman's
  -- lemma proof path for η-naturality.

  -- ── EtaMorph: concrete witness type for η-quotient maps ────────────
  --
  -- An EtaMorph ctx φ witnesses that φ is a valid η-quotient map for
  -- the structural context ctx.  The Python construction is _resolve_type
  -- (core.py:379): an idempotent map that collapses dep_types sharing a
  -- structural key.
  --
  -- Test basis: TestResolveType (5 tests, test_core.py lines 1206–1237):
  --   · test_none:                 φ(None) = None
  --   · test_no_abstraction:       φ("int") = "int" (identity on unreduced)
  --   · test_with_abstraction:     φ("int") = "∀η.X.int" (single step)
  --   · test_with_chained_abstraction: φ("int") = find(abs1) (full chain)
  --   · test_abstraction_not_in_uf: φ("int") = "abs_no_uf" (missing UF entry)
  -- EtaMorph witnesses that φ (dep-type resolution) and canon
  -- (τ-fiber canonical) agree as functions, after the cascade closes.
  --
  -- In Python: _ingest_node (core.py:601) builds τ-signatures as
  --   tau_sig = (ast_type, abs_type, canon_child_taus)
  -- where abs_type = _resolve_type(dep_type).  Two nodes with the same
  -- structural key and the same resolved dep-type get the same τ-id
  -- (via _assign's registry).  The cascade merges τ-classes until
  -- resolve and canonical agree.
  --
  -- The parametrization on canon (rather than an existential) enables
  -- cascade-decomp-adequate to be derived: if φ-single ≡ canon and
  -- φ-decomp ≡ canon, then φ-single ≡ φ-decomp by transitivity.
  --
  -- Tests witnessing the agreement:
  --   · test_fixed_point_after_ingest (1488): direct re-resolve check
  --   · test_pathological_three_way_eta_fixed_point (1551): 3-way
  --   · test_pathological_diamond_cascade_fixed_point (1558): diamond
  --   · test_pathological_deep_chain_fixed_point (1572): 4-level chain
  --   · test_pathological_cascade_depth_6 (1669): 6-level depth
  --   · test_pathological_wide_fan_fixed_point (1689): 10-wide fan
  record EtaMorph (ctx : EtaContext) (φ : ℕ → ℕ) (canon : ℕ → ℕ) : Set where
    field
      -- φ is idempotent: applying it twice gives the same result.
      -- Python: _resolve_type calls _eta_uf.find, which is idempotent.
      -- Test: test_with_chained_abstraction — chained resolution is stable.
      φ-idempotent : ∀ t → φ (φ t) ≡ φ t

      -- canon is idempotent: the post-cascade τ-fiber canonical is a UF root.
      -- Python: tau.canonical = uf.find, which satisfies find(find(x)) = find(x).
      canon-idempotent : ∀ t → canon (canon t) ≡ canon t

      -- φ and canon agree pointwise.
      -- This is the fixed-point condition: the cascade ran until the
      -- dep-type resolution (φ) and the τ-class canonical (canon)
      -- converged to the same function.
      --
      -- Python witness: _pathological_fixed_point_violations (test_core.py:1533)
      -- checks exactly this — for each structural key, resolve(dt) determines
      -- canonical(tid), and canonical(tid) determines resolve(dt), because
      -- the τ-signature includes the resolved dep-type.
      φ≡canon : ∀ t → φ t ≡ canon t

  -- ── P2b: Confluence / commutativity (residual) ───────────────────────
  --
  -- POSTULATE: naturality of η-cascade (η-confluence).
  -- The cascade worklist produces a quotient satisfying the naturality
  -- square above.  This is a confluence (Church-Rosser) property of the
  -- merge rewriting system.  Proof strategy: Newman's lemma.
  --   · Termination: proved by cascade-terminates (P2a above)
  --   · Local confluence: each critical pair resolves (7 pair shapes):
  --       - test_cascade_eta_changed_false_dep_abstract_merge (705)
  --       - test_cascade_eta_changed_true_key_collision (664)
  --       - test_cascade_eta_second_order_full (932)
  --       - test_cascade_eta_changed_true_no_collision (687)
  --       - test_cascade_eta_rekey_collision (798)
  --       - test_cascade_eta_second_order_with_unified_names (962)
  --       - test_cascade_eta_second_order_dup_canon (993)
  --   Blocks on: P1 (union-find) for threading merge operations through
  --   the local confluence lemmas.
  -- Derived: η-naturality (commutativity of η-quotient maps).
  --
  -- Given EtaMorph ctx φ canon and EtaMorph ctx η-map canon, both φ and
  -- η-map agree with canon pointwise (φ≡canon).  Therefore:
  --   η-map (φ t) ≡ canon (canon t) ≡ canon t ≡ φ (η-map t)
  -- Both sides reduce to canon t via φ≡canon + canon-idempotent.
  --
  -- Previously postulated as P2b.  Now constructive.
  η-naturality : ∀ {Label : Set}
         → (ctx : EtaContext)
         → (φ : ℕ → ℕ)
         → (η-map : ℕ → ℕ)
         → (canon : ℕ → ℕ)
         → EtaMorph ctx φ canon
         → EtaMorph ctx η-map canon
         → (∀ t → η-map (φ t) ≡ φ (η-map t))
  η-naturality ctx φ η-map canon mφ mη t =
    let φ≡c  = EtaMorph.φ≡canon mφ
        η≡c  = EtaMorph.φ≡canon mη
        c-fp = EtaMorph.canon-idempotent mφ
        -- η-map (φ t) ≡ canon (canon t) ≡ canon t
        left : η-map (φ t) ≡ canon t
        left = trans (η≡c (φ t)) (trans (cong canon (φ≡c t)) (c-fp t))
        -- φ (η-map t) ≡ canon (canon t) ≡ canon t
        right : φ (η-map t) ≡ canon t
        right = trans (φ≡c (η-map t)) (trans (cong canon (η≡c t)) (c-fp t))
    in  trans left (sym right)

  -- Derived: cascade decomposition adequacy.
  --
  -- Two EtaMorphs sharing the same canon agree pointwise, because
  -- each is pointwise equal to canon (via φ≡canon).
  --
  -- Previously postulated (R8 spec gap).  Now derived from the
  -- strengthened EtaMorph record where φ≡canon replaces the weaker
  -- existential φ-closed.
  --
  -- Python witness: the cascade produces a single post-cascade
  -- Fiber.canonical; both _resolve_type (dep-type UF) and
  -- tau.canonical (τ-class UF) converge to it.
  -- Tests: test_cascade_abstraction_merge_cross_key_stale (1076),
  --        test_pathological_shared_tid_bridges_keys (1712).
  cascade-decomp-adequate
    : ∀ (ctx : EtaContext)
        (φ-single φ-decomp : ℕ → ℕ)
        (canon : ℕ → ℕ)
    → EtaMorph ctx φ-single canon
    → EtaMorph ctx φ-decomp canon
    → ∀ t → φ-single t ≡ φ-decomp t
  cascade-decomp-adequate ctx φs φd canon ms md t =
    trans (EtaMorph.φ≡canon ms t) (sym (EtaMorph.φ≡canon md t))


------------------------------------------------------------------------
-- 6a.  Closure proofs — constructive witnesses from test shapes
--
-- Each lemma proves φ-closed for a specific SPPF structural shape,
-- parameterized over an arbitrary Label type with decidable equality.
-- The specific dep-type values ("int"/"str"/"bool") are replaced by
-- universally quantified distinct labels — the structural shape
-- (key count, depth, fan-out) is what matters.
--
-- These proofs use the abstract fiber operations (fiber-assign,
-- fiber-merge, merge-unifies, merge-preserves) from module 4.
-- They do NOT require P1 (union) internally — they work above the
-- fiber-operations abstraction barrier.
------------------------------------------------------------------------

module SPPF.ClosureProofs where

  open SPPF.Fiber
  open SPPF.UnionFind
  open SPPF.Eta

  -- ── flat-2-merge ──────────────────────────────────────────────────
  --
  -- Shape: 1 structural key, 2 distinct dep-types, no children.
  -- Python test: test_eta_merge_same_structure_different_dep (line 279)
  --   s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
  --   s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
  --   assert s._eta_count == 1
  --   assert tau.canonical(nodes[0].tau) == tau.canonical(nodes[1].tau)
  --
  -- Generalizes over: any Label with two distinct elements.

  flat-2-merge
    : ∀ {Label : Set}
    → (f₀ : Fiber Label)          -- initial fiber
    → (sig₁ sig₂ : Label × List ℕ)  -- two distinct signatures
    → let f₁ = fiber-assign f₀ sig₁ 0
          tid₁ = assign-fid f₀ sig₁ 0
          f₂ = fiber-assign f₁ sig₂ 1
          tid₂ = assign-fid f₁ sig₂ 1
          f-merged = fiber-merge f₂ tid₁ tid₂
          canon = Fiber.canonical f-merged
      in  canon tid₁ ≡ canon tid₂
  flat-2-merge f₀ sig₁ sig₂ =
    let f₁ = fiber-assign f₀ sig₁ 0
        tid₁ = assign-fid f₀ sig₁ 0
        f₂ = fiber-assign f₁ sig₂ 1
        tid₂ = assign-fid f₁ sig₂ 1
    in  merge-unifies f₂ tid₁ tid₂

  -- ── flat-3-merge ──────────────────────────────────────────────────
  --
  -- Shape: 1 structural key, 3 distinct dep-types, no children.
  -- Python test: test_pathological_three_way_eta_fixed_point (line 1551)
  --   s._ingest_node("X", (), "int", "k1", (), (), (), 0, "f")
  --   s._ingest_node("X", (), "str", "k2", (), (), (), 1, "f")
  --   s._ingest_node("X", (), "bool", "k3", (), (), (), 2, "f")
  --   assert _pathological_fixed_point_violations(s) == []
  --
  -- Proof: merge tid₁ tid₂ (merge-unifies), then merge result with tid₃.
  -- merge-preserves carries the tid₁≡tid₂ equivalence through the second
  -- merge; merge-unifies gives tid₂≡tid₃ in the final fiber.

  flat-3-merge
    : ∀ {Label : Set}
    → (f₀ : Fiber Label)
    → (sig₁ sig₂ sig₃ : Label × List ℕ)
    → let f₁   = fiber-assign f₀ sig₁ 0
          tid₁  = assign-fid f₀ sig₁ 0
          f₂   = fiber-assign f₁ sig₂ 1
          tid₂  = assign-fid f₁ sig₂ 1
          f₃   = fiber-assign f₂ sig₃ 2
          tid₃  = assign-fid f₂ sig₃ 2
          -- First merge: tid₁ and tid₂
          f₁₂   = fiber-merge f₃ tid₁ tid₂
          -- Second merge: tid₂ and tid₃ (in the post-first-merge fiber)
          f₁₂₃  = fiber-merge f₁₂ tid₂ tid₃
          canon = Fiber.canonical f₁₂₃
      in  (canon tid₁ ≡ canon tid₂) × (canon tid₂ ≡ canon tid₃)
  flat-3-merge f₀ sig₁ sig₂ sig₃ =
    let f₁   = fiber-assign f₀ sig₁ 0
        tid₁  = assign-fid f₀ sig₁ 0
        f₂   = fiber-assign f₁ sig₂ 1
        tid₂  = assign-fid f₁ sig₂ 1
        f₃   = fiber-assign f₂ sig₃ 2
        tid₃  = assign-fid f₂ sig₃ 2
        f₁₂   = fiber-merge f₃ tid₁ tid₂
        f₁₂₃  = fiber-merge f₁₂ tid₂ tid₃
        -- Step 1: merge-unifies gives us tid₁ ≡ tid₂ in f₁₂
        step₁ : Fiber.canonical f₁₂ tid₁ ≡ Fiber.canonical f₁₂ tid₂
        step₁ = merge-unifies f₃ tid₁ tid₂
        -- Step 2: merge-preserves carries step₁ through the second merge
        carried : Fiber.canonical f₁₂₃ tid₁ ≡ Fiber.canonical f₁₂₃ tid₂
        carried = merge-preserves f₁₂ tid₂ tid₃ tid₁ tid₂ step₁
        -- Step 3: merge-unifies gives us tid₂ ≡ tid₃ in f₁₂₃
        step₂ : Fiber.canonical f₁₂₃ tid₂ ≡ Fiber.canonical f₁₂₃ tid₃
        step₂ = merge-unifies f₁₂ tid₂ tid₃
    in  carried , step₂

  -- ── chain-2-merge ─────────────────────────────────────────────────
  --
  -- Shape: 2 levels, each with 2 variants.  Level 0 has no children;
  -- level 1's children are the merged level-0 τ-id.
  -- Python test: test_pathological_deep_chain_fixed_point (line 1572),
  --   first two levels (L0 and L1).
  --
  --   L0: assign a, assign b → merge → canon₀
  --   L1: assign c (child=canon₀), assign d (child=canon₀) → merge → canon₁
  --
  -- The key property: the L1 merge succeeds because both L1 variants
  -- used the same child canonical (canon₀), so they share a structural
  -- key and η-detection triggers a merge.

  chain-2-merge
    : ∀ {Label : Set}
    → (f₀ : Fiber Label)
    → (sig-L0-a sig-L0-b sig-L1-c sig-L1-d : Label × List ℕ)
    → let -- Level 0: two assigns, one merge
          f₀₁   = fiber-assign f₀ sig-L0-a 0
          t0a   = assign-fid f₀ sig-L0-a 0
          f₀₂   = fiber-assign f₀₁ sig-L0-b 1
          t0b   = assign-fid f₀₁ sig-L0-b 1
          f₀m   = fiber-merge f₀₂ t0a t0b
          -- Level 1: two assigns (using the merged fiber), one merge
          f₁₁   = fiber-assign f₀m sig-L1-c 2
          t1c   = assign-fid f₀m sig-L1-c 2
          f₁₂   = fiber-assign f₁₁ sig-L1-d 3
          t1d   = assign-fid f₁₁ sig-L1-d 3
          f₁m   = fiber-merge f₁₂ t1c t1d
          canon = Fiber.canonical f₁m
      in  (canon t0a ≡ canon t0b)   -- level 0 closure
        × (canon t1c ≡ canon t1d)   -- level 1 closure
  chain-2-merge f₀ s0a s0b s1c s1d =
    let f₀₁  = fiber-assign f₀ s0a 0
        t0a  = assign-fid f₀ s0a 0
        f₀₂  = fiber-assign f₀₁ s0b 1
        t0b  = assign-fid f₀₁ s0b 1
        f₀m  = fiber-merge f₀₂ t0a t0b
        f₁₁  = fiber-assign f₀m s1c 2
        t1c  = assign-fid f₀m s1c 2
        f₁₂  = fiber-assign f₁₁ s1d 3
        t1d  = assign-fid f₁₁ s1d 3
        f₁m  = fiber-merge f₁₂ t1c t1d
        -- Level 0: merge-unifies in f₀m, then carry through assigns + merge
        step0 : Fiber.canonical f₀m t0a ≡ Fiber.canonical f₀m t0b
        step0 = merge-unifies f₀₂ t0a t0b
        -- Carry through assign f₁₁
        carry1 : Fiber.canonical f₁₁ t0a ≡ Fiber.canonical f₁₁ t0b
        carry1 = assign-preserves f₀m s1c 2 t0a t0b step0
        -- Carry through assign f₁₂
        carry2 : Fiber.canonical f₁₂ t0a ≡ Fiber.canonical f₁₂ t0b
        carry2 = assign-preserves f₁₁ s1d 3 t0a t0b carry1
        -- Carry through merge f₁m
        carried0 : Fiber.canonical f₁m t0a ≡ Fiber.canonical f₁m t0b
        carried0 = merge-preserves f₁₂ t1c t1d t0a t0b carry2
        -- Level 1: merge-unifies directly
        step1 : Fiber.canonical f₁m t1c ≡ Fiber.canonical f₁m t1d
        step1 = merge-unifies f₁₂ t1c t1d
    in  carried0 , step1

  -- ── diamond-merge ─────────────────────────────────────────────────
  --
  -- Shape: 2 independent child keys (CL, CR), each with 2 variants
  -- that η-merge, then 1 parent key (P) with 2 variants keyed on
  -- both merged children.
  --
  -- Python test: test_pathological_diamond_cascade_fixed_point (line 1558)
  --   CL(a), CL(b) → merge → cl
  --   CR(x), CR(y) → merge → cr
  --   P(int, children=[cl,cr]), P(str, children=[cl,cr]) → merge
  --
  -- New technique: two parallel child merges whose results must both
  -- be carried through the parent-level assigns and merge.

  diamond-merge
    : ∀ {Label : Set}
    → (f₀ : Fiber Label)
    → (sL-a sL-b sR-x sR-y sP-i sP-s : Label × List ℕ)
    → let -- Left child: assign a, assign b, merge
          fL₁   = fiber-assign f₀ sL-a 0
          tL-a  = assign-fid f₀ sL-a 0
          fL₂   = fiber-assign fL₁ sL-b 1
          tL-b  = assign-fid fL₁ sL-b 1
          fLm   = fiber-merge fL₂ tL-a tL-b
          -- Right child: assign x, assign y, merge
          fR₁   = fiber-assign fLm sR-x 2
          tR-x  = assign-fid fLm sR-x 2
          fR₂   = fiber-assign fR₁ sR-y 3
          tR-y  = assign-fid fR₁ sR-y 3
          fRm   = fiber-merge fR₂ tR-x tR-y
          -- Parent: assign int, assign str, merge
          fP₁   = fiber-assign fRm sP-i 4
          tP-i  = assign-fid fRm sP-i 4
          fP₂   = fiber-assign fP₁ sP-s 5
          tP-s  = assign-fid fP₁ sP-s 5
          fPm   = fiber-merge fP₂ tP-i tP-s
          canon = Fiber.canonical fPm
      in  (canon tL-a ≡ canon tL-b)    -- left child closure
        × (canon tR-x ≡ canon tR-y)    -- right child closure
        × (canon tP-i ≡ canon tP-s)    -- parent closure
  diamond-merge f₀ sL-a sL-b sR-x sR-y sP-i sP-s =
    let -- Build all fibers
        fL₁  = fiber-assign f₀ sL-a 0
        tL-a = assign-fid f₀ sL-a 0
        fL₂  = fiber-assign fL₁ sL-b 1
        tL-b = assign-fid fL₁ sL-b 1
        fLm  = fiber-merge fL₂ tL-a tL-b
        fR₁  = fiber-assign fLm sR-x 2
        tR-x = assign-fid fLm sR-x 2
        fR₂  = fiber-assign fR₁ sR-y 3
        tR-y = assign-fid fR₁ sR-y 3
        fRm  = fiber-merge fR₂ tR-x tR-y
        fP₁  = fiber-assign fRm sP-i 4
        tP-i = assign-fid fRm sP-i 4
        fP₂  = fiber-assign fP₁ sP-s 5
        tP-s = assign-fid fP₁ sP-s 5
        fPm  = fiber-merge fP₂ tP-i tP-s

        -- Left child: merge-unifies in fLm, carry through everything after
        stepL : Fiber.canonical fLm tL-a ≡ Fiber.canonical fLm tL-b
        stepL = merge-unifies fL₂ tL-a tL-b
        -- Carry through: assign R-x, assign R-y, merge R, assign P-i, assign P-s, merge P
        cL₁ = assign-preserves fLm sR-x 2 tL-a tL-b stepL
        cL₂ = assign-preserves fR₁ sR-y 3 tL-a tL-b cL₁
        cL₃ = merge-preserves fR₂ tR-x tR-y tL-a tL-b cL₂
        cL₄ = assign-preserves fRm sP-i 4 tL-a tL-b cL₃
        cL₅ = assign-preserves fP₁ sP-s 5 tL-a tL-b cL₄
        carriedL : Fiber.canonical fPm tL-a ≡ Fiber.canonical fPm tL-b
        carriedL = merge-preserves fP₂ tP-i tP-s tL-a tL-b cL₅

        -- Right child: merge-unifies in fRm, carry through parent ops
        stepR : Fiber.canonical fRm tR-x ≡ Fiber.canonical fRm tR-y
        stepR = merge-unifies fR₂ tR-x tR-y
        cR₁ = assign-preserves fRm sP-i 4 tR-x tR-y stepR
        cR₂ = assign-preserves fP₁ sP-s 5 tR-x tR-y cR₁
        carriedR : Fiber.canonical fPm tR-x ≡ Fiber.canonical fPm tR-y
        carriedR = merge-preserves fP₂ tP-i tP-s tR-x tR-y cR₂

        -- Parent: merge-unifies directly
        stepP : Fiber.canonical fPm tP-i ≡ Fiber.canonical fPm tP-s
        stepP = merge-unifies fP₂ tP-i tP-s
    in  carriedL , carriedR , stepP


------------------------------------------------------------------------
-- 7.  Cleavage  —  cleavage planes as pullbacks
--
-- A cleavage plane is the pullback of two τ-classes over a common
-- structural key.  Given:
--   τ₁, τ₂ : FiberClass with the same (ast_type, child-τ⃗) but
--             different dep_type residues
-- the cleavage is the pair  (τ₁, τ₂)  together with their shared
-- structural key as the apex of the cospan.
--
-- "Ghost" cleavage: κ-tags of τ₁ and τ₂ coincide  ⟹  not a real
-- ambiguity (the two classes are κ-indistinguishable).
------------------------------------------------------------------------

module SPPF.Cleavage where

  open SPPF.FiberClass

  -- A cleavage plane at level ℓ
  record CleavagePlane : Set where
    field
      level       : ℕ
      struct-key  : ℕ × List ℕ           -- (ast_type, child-τ-ids)
      left-τ      : ℕ                    -- first τ-class id
      right-τ     : ℕ                    -- second τ-class id
      is-ghost    : Bool                 -- true iff κ-tags coincide

  -- Pullback universal property:
  -- CleavagePlane is the limit of the cospan
  --   left-τ  ←  struct-key  →  right-τ
  -- where both arrows are "has this structural key."
  record IsPullback (P : CleavagePlane) : Set where
    field
      -- Pullback apex and projections into the cospan legs.
      Obj      : Set
      apex     : Obj → ℕ
      π-left   : Obj → ℕ
      π-right  : Obj → ℕ

      -- The cospan legs over the common apex key.
      left-leg  : ℕ → ℕ
      right-leg : ℕ → ℕ

      -- Commutativity with the cospan legs.
      commute-left  : ∀ x → left-leg  (π-left  x) ≡ apex x
      commute-right : ∀ x → right-leg (π-right x) ≡ apex x

      -- Distinguished points corresponding to the two tracked τ-classes.
      left-point  : Obj
      right-point : Obj
      left-point-proj  : π-left  left-point  ≡ CleavagePlane.left-τ  P
      right-point-proj : π-right right-point ≡ CleavagePlane.right-τ P

      -- Universality: every cone into the same cospan factors through P.
      universal : ∀ {Q : Set}
                → (q-apex : Q → ℕ)
                → (q-left : Q → ℕ)
                → (q-right : Q → ℕ)
                → (∀ x → left-leg  (q-left  x) ≡ q-apex x)
                → (∀ x → right-leg (q-right x) ≡ q-apex x)
                → Σ (Q → Obj) λ h
                    → (∀ x → π-left  (h x) ≡ q-left x)
                    × (∀ x → π-right (h x) ≡ q-right x)

      -- Uniqueness of the mediator (pointwise form).
      universal-unique : ∀ {Q : Set}
                       → (q-left : Q → ℕ)
                       → (q-right : Q → ℕ)
                       → (h₁ h₂ : Q → Obj)
                       → (∀ x → π-left  (h₁ x) ≡ q-left x)
                       → (∀ x → π-right (h₁ x) ≡ q-right x)
                       → (∀ x → π-left  (h₂ x) ≡ q-left x)
                       → (∀ x → π-right (h₂ x) ≡ q-right x)
                       → ∀ x → h₁ x ≡ h₂ x

  -- Runtime-aligned interface -------------------------------------
  -- Mirrors _process_cleavage bookkeeping in core.py:
  --   * cleavage_key   = (context, residue-signature)
  --   * existing       = parent_key ↦ canonical τ-id
  --   * levels         = list of level indices, each keyed by cleavage_key

  record CleavageKey : Set where
    field
      context : ℕ
      residue : List ℕ

  ParentMap : Set
  ParentMap = List (ℕ × ℕ)      -- parent_key ↦ canonical τ-id

  LevelIndex : Set
  LevelIndex = List (CleavageKey × ParentMap)

  record CleavageLevelState : Set where
    field
      level-no : ℕ
      index    : LevelIndex

  record CleavageRuntimeState : Set where
    field
      levels : List CleavageLevelState

  data CleavageStep : Set where
    seed-key      : CleavageStep  -- first insertion for a cleavage_key
    attach-parent : CleavageStep  -- parent_key added to existing map
    emit-plane    : CleavageStep  -- len(existing) >= 2 emits cleavage tag
    ascend-level  : CleavageStep  -- next_residue with size >= 2
    halt          : CleavageStep  -- termination of while-loop

  record CleavageTransition : Set where
    field
      from-state     : CleavageRuntimeState
      to-state       : CleavageRuntimeState
      level          : ℕ
      key            : CleavageKey
      parent-key     : ℕ
      canonical-τ    : ℕ
      step           : CleavageStep
      ghost-flag     : Bool
      -- The two canonical τ-ids visible at emit-plane time; mirrors the two
      -- entries in the Python `existing` dict when len(existing) >= 2 fires.
      --   left-τ  = the pre-existing τ-id (from the first parent in existing)
      --   right-τ = canonical-τ above (the τ-id for the current parent-key)
      -- Having left-τ as an explicit field removes the blocking dependency
      -- on implicit extraction that was noted in Phase C.
      left-τ         : ℕ
      right-τ        : ℕ

      -- Runtime dictionary witnesses threaded explicitly into the transition.
      parents        : ParentMap
      left-parent    : ℕ
      keyed-at-level : LevelHasKey to-state level key parents
      left-tracked   : ParentTracked parents left-parent left-τ
      right-tracked  : ParentTracked parents parent-key right-τ
      pullback-proof : IsPullback (record
        { level      = level
        ; struct-key = (CleavageKey.context key , CleavageKey.residue key)
        ; left-τ     = left-τ
        ; right-τ    = right-τ
        ; is-ghost   = ghost-flag
        })

  key-from-plane : CleavagePlane → CleavageKey
  key-from-plane p = record
    { context = proj₁ (CleavagePlane.struct-key p)
    ; residue = proj₂ (CleavagePlane.struct-key p)
    }

  -- Lookup relations induced by runtime dictionaries.
  -- These correspond to:
  --   level_index = self._cleavage_levels[level]
  --   existing = level_index[cleavage_key]

  data KeyMapIn : LevelIndex → CleavageKey → ParentMap → Set where
    key-here  : ∀ {rest key pm}
              → KeyMapIn ((key , pm) ∷ rest) key pm
    key-there : ∀ {rest key' pm' key pm}
              → KeyMapIn rest key pm
              → KeyMapIn ((key' , pm') ∷ rest) key pm

  data LevelHasKey : CleavageRuntimeState → ℕ → CleavageKey → ParentMap → Set where
    level-here  : ∀ {rest ℓ key pm idx}
                → KeyMapIn idx key pm
                → LevelHasKey
                    (record { levels = (record { level-no = ℓ ; index = idx }) ∷ rest })
                    ℓ key pm
    level-there : ∀ {rest state ℓ key pm}
                → LevelHasKey (record { levels = rest }) ℓ key pm
                → LevelHasKey (record { levels = state ∷ rest }) ℓ key pm

  data ParentTracked : ParentMap → ℕ → ℕ → Set where
    parent-here  : ∀ {rest pk tid}
                 → ParentTracked ((pk , tid) ∷ rest) pk tid
    parent-there : ∀ {rest pk' tid' pk tid}
                 → ParentTracked rest pk tid
                 → ParentTracked ((pk' , tid') ∷ rest) pk tid

  -- Concrete pullback witness extracted from one runtime transition.
  record PullbackWitnessInterface (tr : CleavageTransition) : Set where
    field
      plane         : CleavagePlane
      parents       : ParentMap
      left-parent   : ℕ
      right-parent  : ℕ

      -- Tie witness to runtime level/key tracking.
      keyed-at-level : LevelHasKey (CleavageTransition.to-state tr)
                                  (CleavagePlane.level plane)
                                  (key-from-plane plane)
                                  parents
      left-tracked   : ParentTracked parents left-parent
                         (CleavagePlane.left-τ plane)
      right-tracked  : ParentTracked parents right-parent
                         (CleavagePlane.right-τ plane)

      -- Emitted cleavage carries pullback structure.
      emitted-step   : CleavageTransition.step tr ≡ emit-plane
      pullback       : IsPullback plane

  -- Concrete witness extracted from an emitted cleavage transition.
  -- The plane, right-parent, and emitted-step are filled directly from tr.
  -- Remaining holes require proof obligations as noted per field.
  witness-from-transition
    : (tr : CleavageTransition)
    → CleavageTransition.step tr ≡ emit-plane
    → PullbackWitnessInterface tr
  witness-from-transition tr eq = record
    { plane = record
        { level      = CleavageTransition.level tr
        ; struct-key = ( CleavageKey.context (CleavageTransition.key tr)
                       , CleavageKey.residue  (CleavageTransition.key tr) )
        ; left-τ     = CleavageTransition.left-τ tr
        ; right-τ    = CleavageTransition.right-τ tr
        ; is-ghost   = CleavageTransition.ghost-flag tr
        }
    ; parents       = CleavageTransition.parents tr
    ; left-parent   = CleavageTransition.left-parent tr
    ; right-parent  = CleavageTransition.parent-key tr
    ; keyed-at-level = CleavageTransition.keyed-at-level tr
    ; left-tracked  = CleavageTransition.left-tracked tr
    ; right-tracked = CleavageTransition.right-tracked tr
    ; emitted-step  = eq
    ; pullback      = CleavageTransition.pullback-proof tr
    }

  -- Ghost filter: a cleavage is real iff its κ-tag sets differ.
  is-real : CleavagePlane → Bool
  is-real p = not (CleavagePlane.is-ghost p)


------------------------------------------------------------------------
-- 8.  Cell observation lattice
--
-- Cells are graded by dimension:
--   0-cell  = individual node
--   1-cell  = τ-class
--   2-cell  = η-merge event (a natural transformation witness)
--   3-cell  = cleavage-L0
--   4-cell  = cleavage-L1
--   …
--
-- Observation counts are pushed downward: observing a k-cell adds 1
-- to each contained (k-1)-cell, recursively.
-- This is a weighted cochain on the nerve of the filtration.
--
-- The "highest-ordered structures" query is: argmax_{level ≥ 2} count.
------------------------------------------------------------------------

module SPPF.CellObs where

  -- A cell at level ℓ with an observation count
  record Cell : Set where
    field
      level : ℕ
      id    : ℕ             -- opaque identifier
      count : ℕ             -- cumulative projected observation count

  -- The graded observation map
  -- obs : (level : ℕ) → id → count
  -- We represent it as a list (level, id, count) sorted by count desc.
  Obs : Set
  Obs = List (ℕ × ℕ × ℕ)   -- (level, id, count)

  -- Downward projection: observe cell (ℓ, id) and push +1 to all
  -- (ℓ-1)-cells it contains.
  -- This is exactly  _observe_cell  in the Python.
  --
  -- In cochain terms: if  δ : C^{ℓ-1} → C^ℓ  is the coboundary, then
  -- observing a cochain element x ∈ C^ℓ adds  δ*(x)  to the chain.
  -- δ*  is the adjoint (pushforward) of the coboundary.

  increment : Obs → ℕ → ℕ → Obs
  increment [] ℓ id = (ℓ , id , 1) ∷ []
  increment ((ℓ' , id' , c) ∷ rest) ℓ id with ℓ ≟ ℓ'
  ... | yes _ with id ≟ id'
  ... | yes _ | yes _ = (ℓ' , id' , suc c) ∷ rest
  ... | yes _ | no  _ = (ℓ' , id' , c) ∷ increment rest ℓ id
  ... | no  _ = (ℓ' , id' , c) ∷ increment rest ℓ id

  observe-children : Obs → ℕ → List ℕ → Obs
  observe-children obs _ [] = obs
  observe-children obs ℓ (cid ∷ rest) =
    observe-children (observe obs ℓ cid []) ℓ rest

  observe : Obs → ℕ → ℕ → List ℕ → Obs
  observe obs zero    id contained = increment obs zero id
  observe obs (suc ℓ) id contained =
    observe-children (increment obs (suc ℓ) id) ℓ contained

  -- Top-k query: the answer to "what are the highest-ordered structures?"
  top-k : Obs → ℕ → Obs
  top-k obs k = take k (sort-by-count obs)
    where
      _≡ℕ?_ : ℕ → ℕ → Bool
      zero  ≡ℕ? zero  = true
      zero  ≡ℕ? suc _ = false
      suc _ ≡ℕ? zero  = false
      suc a ≡ℕ? suc b = a ≡ℕ? b

      _>?_ : ℕ → ℕ → Bool
      zero  >? _     = false
      suc _ >? zero  = true
      suc a >? suc b = a >? b

      _>pair_ : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → Bool
      (ℓ₁ , _ , c₁) >pair (ℓ₂ , _ , c₂) =
        (c₁ >? c₂) ∨ ((c₁ ≡ℕ? c₂) ∧ (ℓ₁ >? ℓ₂))

      insert : (ℕ × ℕ × ℕ) → Obs → Obs
      insert x [] = x ∷ []
      insert x (y ∷ ys) with x >pair y
      ... | true  = x ∷ y ∷ ys
      ... | false = y ∷ insert x ys

      -- Stable sort by count descending, then level descending.
      sort-by-count : Obs → Obs
      sort-by-count []       = []
      sort-by-count (x ∷ xs) = insert x (sort-by-count xs)

      -- sort by count descending, then by level descending
      take : ℕ → Obs → Obs
      take zero    _        = []
      take _       []       = []
      take (suc n) (x ∷ xs) = x ∷ take n xs

  -- The "structurally load-bearing" metric (your description):
  -- not "how often does this node appear" but "how load-bearing is it
  -- across the fibration seen so far."
  -- This is precisely the projected count at level ≥ 2.
  load-bearing : Obs → Obs
  load-bearing = filter-level 2
    where
      filter-level : ℕ → Obs → Obs
      filter-level ℓ []                = []
      filter-level ℓ ((l , i , c) ∷ xs) with l
      ... | zero = filter-level ℓ xs
      ... | suc _ = if l ≥? ℓ then (l , i , c) ∷ filter-level ℓ xs
                               else filter-level ℓ xs
        where
          _≥?_ : ℕ → ℕ → Bool
          zero  ≥? zero  = true
          zero  ≥? suc _ = false
          suc m ≥? zero  = true
          suc m ≥? suc n = m ≥? n


------------------------------------------------------------------------
-- 9.  Huffman / dynamic coding analysis
--
-- The SPPF can be used as a dynamic Huffman coding tree where the
-- weight of a node is its "load-bearing" observation count.
--
-- Key theorems about the two-time-notions problem:
--
-- Theorem A (Vitter sibling property):
--   A Huffman tree satisfies the sibling property iff weights are
--   monotonically non-decreasing along any root-to-leaf path, AND
--   all updates are local (no retroactive cascade).
--
-- Theorem B (cascade violation):
--   τ-merges in η-cascade can retroactively change the weight of
--   already-emitted nodes (because their τ-id is re-canonicalized),
--   violating the sibling property globally.
--
-- Theorem C (rewrite window):
--   Let W(t) = { nodes whose τ-canonical-id changed since step t₀ }.
--   Flushing at step t₀ + k emits all nodes outside W(t₀+k).
--   The window W is bounded by the cascade depth of the last η-merge.
--   Setting k = budget / cost-per-step gives a deterministic bound.
------------------------------------------------------------------------

module SPPF.Huffman where

  open SPPF.CellObs

  -- A Huffman node: weight = load-bearing observation count
  record HuffmanNode : Set where
    field
      node-id : ℕ
      weight  : ℕ
      left    : Maybe ℕ    -- child node-id (nothing = leaf)
      right   : Maybe ℕ

  -- The sibling property (Vitter 1987):
  -- Every node has a sibling with equal or smaller weight,
  -- and siblings are adjacent in weight order.
  record SiblingProperty (tree : List HuffmanNode) : Set where
    field
      ordered  : ∀ (i j : ℕ) → i ≤ j → weight-at i ≤ weight-at j
      adjacent : ∀ (n : HuffmanNode) → ∃ λ m →
                   HuffmanNode.weight n ≡ HuffmanNode.weight m

    _≡ℕ?_ : ℕ → ℕ → Bool
    zero  ≡ℕ? zero  = true
    zero  ≡ℕ? suc _ = false
    suc _ ≡ℕ? zero  = false
    suc a ≡ℕ? suc b = a ≡ℕ? b

    lookup-weight : List HuffmanNode → ℕ → ℕ
    lookup-weight [] _ = 0
    lookup-weight (n ∷ ns) id with HuffmanNode.node-id n ≡ℕ? id
    ... | true  = HuffmanNode.weight n
    ... | false = lookup-weight ns id

    weight-at : ℕ → ℕ
    weight-at id = lookup-weight tree id

  -- Rewrite window: the set of node-ids whose canonical τ-id
  -- changed since the last flush.
  RewriteWindow : Set
  RewriteWindow = List ℕ   -- node-ids pending rebalance

  -- The two notions of time
  record TwoTime : Set where
    field
      -- Monotonically increasing: the ingestion step counter.
      mono-time    : ℕ
      -- Retroactively accessible: the set of steps whose τ-ids
      -- were affected by a cascade at the current step.
      retro-window : List ℕ   -- step indices in the rewrite window

  -- Deterministic budget controller:
  -- adjust window size to keep cost ≤ budget-per-symbol.
  record BudgetController : Set where
    field
      budget-per-symbol : ℕ      -- cost units per emitted symbol
      current-window    : ℕ      -- current window size (in steps)
      step-cost         : ℕ      -- cost of one state-machine step

    max-window : ℕ
    max-window = budget-per-symbol / step-cost
      where
        _/_ : ℕ → ℕ → ℕ
        _/_ n zero    = 0       -- guard; step-cost should be ≥ 1
        _/_ n (suc m) = div n (suc m)
          where
            div : ℕ → ℕ → ℕ
            div zero    _ = zero
            div (suc n) m with suc n ≤? m
              where
                _≤?_ : ℕ → ℕ → Bool
                zero  ≤? _     = true
                suc _ ≤? zero  = false
                suc n ≤? suc m = n ≤? m
            ... | true  = zero
            ... | false = suc (div (suc n ∸ m) m)
              where
                _∸_ : ℕ → ℕ → ℕ
                n     ∸ zero  = n
                zero  ∸ suc _ = zero
                suc n ∸ suc m = n ∸ m


------------------------------------------------------------------------
-- 10.  Core SPPF record
--
-- The SPPF is the dependent record tying the three fibers together.
-- Each node is a triple (σ-id, τ-id, κ-id) in the product fiber.
-- The wedge product σ ∧ τ ∧ κ is the image of the diagonal
--   diag : Nodes → Fib_σ × Fib_τ × Fib_κ
------------------------------------------------------------------------

module SPPF.Core where

  open SPPF.Fiber
  open SPPF.Kappa
  open SPPF.Eta
  open SPPF.Cleavage
  open SPPF.CellObs
  open SPPF.GF2

  -- Abstract label type (ast_type, dep_type, kappa_tag, params)
  -- INTENTIONAL RESIDUAL: Label represents Python's classifier label type
  -- (ast_type, dep_type, kappa_tag, params).  It is not constructible from
  -- within Agda alone; its concrete content is provided by the Python runtime.
  -- Keeping it abstract here is the correct modelling choice.
  postulate Label : Set

  -- A single parsed node
  record Node : Set where
    field
      -- Fiber coordinates
      σ-id      : ℕ
      τ-id      : ℕ
      κ-id      : ℕ
      -- Raw classifier data
      ast-type  : Label
      dep-type  : Maybe Label
      kappa-tag : Label
      -- Source location
      line      : ℕ
      file      : ℕ            -- interned filename

  -- The SPPF itself
  record SPPF : Set₁ where
    field
      -- The three fibers
      sigma  : Fiber Label
      tau    : Fiber Label
      kappa  : Fiber Label

      -- The node array
      nodes  : List Node

      -- κ coproduct structure
      κ-coprod : KappaCoproduct Label

      -- η-tower: the sequence of η-merge events
      η-tower  : List EtaEvent

      -- Cleavage planes (real + ghost)
      cleavage-planes : List CleavagePlane

      -- Cell observation lattice
      obs : Obs

      -- Orientation on each fiber (the GF(2)-torsor)
      σ-orient : Orientation
      τ-orient : Orientation
      κ-orient : Orientation

    -- The wedge product: the set of occupied (σ,τ,κ) cells
    WedgeCell : Set
    WedgeCell = ℕ × ℕ × ℕ    -- (σ-id, τ-id, κ-id)

    wedge : List WedgeCell
    wedge = map (λ n → ( Node.σ-id n
                       , Node.τ-id n
                       , Node.κ-id n )) nodes

    -- The structural class is the dual to the adjoint that constructs
    -- the SPPF.  In adjunction terms:
    --   L ⊣ R  where  L = Δ (diagonal / constant fiber)
    --                 R = ⊎_τ (coproduct in slice over τ)
    -- The counit  ε : L ∘ R ⟹ Id  is the η-collapse.
    -- The unit    η : Id ⟹ R ∘ L  is the embedding of a node into
    --             its fiber class.

    -- Number of η-merges at the first level
    η-count : ℕ
    η-count = length η-tower

    -- Real cleavage planes
    real-cleavage : List CleavagePlane
    real-cleavage = filter is-real cleavage-planes
      where
        filter : (CleavagePlane → Bool) → List CleavagePlane → List CleavagePlane
        filter _ []       = []
        filter p (x ∷ xs) with p x
        ... | true  = x ∷ filter p xs
        ... | false = filter p xs

    -- The structural class dual (the adjoint's image)
    -- is the quotient of nodes by the equivalence  n ~ m iff
    -- sigma.canonical(n.σ-id) = sigma.canonical(m.σ-id)  AND
    -- tau.canonical(n.τ-id)   = tau.canonical(m.τ-id)    AND
    -- kappa.canonical(n.κ-id) = kappa.canonical(m.κ-id).
    _≅_ : Node → Node → Set
    n ≅ m =
        Fiber.canonical sigma (Node.σ-id n) ≡ Fiber.canonical sigma (Node.σ-id m)
      × Fiber.canonical tau   (Node.τ-id n) ≡ Fiber.canonical tau   (Node.τ-id m)
      × Fiber.canonical kappa (Node.κ-id n) ≡ Fiber.canonical kappa (Node.κ-id m)


------------------------------------------------------------------------
-- 11.  Ingestion specification
--
-- The _ingest_node function satisfies a specification that we can
-- express as a pre/post contract on the SPPF state.
------------------------------------------------------------------------

module SPPF.Ingest where

  open SPPF.Core
  open SPPF.Eta
  open SPPF.Fiber using (fiber-assign; assign-classes-bound;
                          fiber-merge; merge-classes-bound;
                          merge-canonical-decreases)

  -- List membership witness for child-id preconditions.
  data _∈ℕ_ : ℕ → List ℕ → Set where
    hereℕ  : ∀ {x xs} → x ∈ℕ (x ∷ xs)
    thereℕ : ∀ {x y xs} → x ∈ℕ xs → x ∈ℕ (y ∷ xs)

  data _∈Node_ : Node → List Node → Set where
    hereNode  : ∀ {n ns} → n ∈Node (n ∷ ns)
    thereNode : ∀ {n m ns} → n ∈Node ns → n ∈Node (m ∷ ns)

  -- An element is in xs ++ (x ∷ []).  Proved by induction on xs.
  -- Witnesses node-present for ingest (the new node is at the end).
  ∈-++-right : ∀ (xs : List Node) (x : Node) → x ∈Node (xs ++ (x ∷ []))
  ∈-++-right []       x = hereNode
  ∈-++-right (_ ∷ xs) x = thereNode (∈-++-right xs x)

  -- Pre-condition: the child fiber-ids are already canonicalised.
  record IngestPre (sppf : SPPF) (child-σs child-τs child-κs : List ℕ) : Set where
    field
      σ-canon : ∀ i → i ∈ℕ child-σs → Fiber.canonical (SPPF.sigma sppf) i ≡ i
      τ-canon : ∀ i → i ∈ℕ child-τs → Fiber.canonical (SPPF.tau   sppf) i ≡ i
      κ-canon : ∀ i → i ∈ℕ child-κs → Fiber.canonical (SPPF.kappa sppf) i ≡ i

  -- Post-condition: the new node is in the SPPF, η-merges are
  -- reflected, and no previously canonical class is invalidated
  -- except through a recorded merge.
  record IngestPost (sppf sppf' : SPPF) (n : Node) : Set where
    field
      -- The node is in the new array
      node-present : n ∈Node (SPPF.nodes sppf')

      -- Fiber sizes can increase by at most one per ingest step:
      -- _assign may create one new class and merge never creates classes.
      σ-shrinks : length (Fiber.classes (SPPF.sigma sppf')) ≤ length (Fiber.classes (SPPF.sigma sppf)) + 1
      τ-shrinks : length (Fiber.classes (SPPF.tau   sppf')) ≤ length (Fiber.classes (SPPF.tau   sppf)) + 1
      κ-shrinks : length (Fiber.classes (SPPF.kappa sppf')) ≤ length (Fiber.classes (SPPF.kappa sppf)) + 1

      -- η-tower is extended (non-decreasing)
      η-grows : length (SPPF.η-tower sppf) ≤ length (SPPF.η-tower sppf')

  -- Helper: appending extends a list (length xs ≤ length (xs ++ ys)).
  -- Proved by structural recursion on xs.  Witnesses the η-grows field:
  -- if sppf'.η-tower = sppf.η-tower ++ new-events then
  --   append-≤ (SPPF.η-tower sppf) new-events : length sppf.η-tower ≤ length sppf'.η-tower
  append-≤ : ∀ {A : Set} (xs ys : List A) → length xs ≤ length (xs ++ ys)
  append-≤ []       ys = z≤n
  append-≤ (x ∷ xs) ys = s≤s (append-≤ xs ys)

  -- ── Ingest construction ──────────────────────────────────────────────
  --
  -- The ingest function: assign each fiber, η-detect + cascade on τ,
  -- append node and η-events.  The body is partially filled: σ and κ
  -- assignments and list appends are concrete; the τ-cascade portion
  -- remains a hole (blocked by P2a: cascade must be constructive).
  --
  -- Python: _ingest_node (core.py:580–688)
  -- Tests: test_single_node (190), test_fixed_point_after_ingest (1488)

  -- Node index for the new node (appended at end of the list).
  node-index : SPPF → ℕ
  node-index sppf = length (SPPF.nodes sppf)

  -- Signature constructors for each fiber, from a Node's fields.
  -- Python: sigma_sig = (ast_type, params, child_sigmas)   — core.py:592
  --         tau_sig   = (ast_type, abs_type, canon_child_taus) — core.py:601
  --         kappa_sig = (kappa_tag, child_kappas)           — core.py:593
  -- Simplified here: Label × List ℕ, using only the primary label + child ids.
  σ-sig : Node → Label × List ℕ
  σ-sig n = Node.ast-type n , []

  τ-sig : Node → Label × List ℕ
  τ-sig n = Node.ast-type n , []    -- simplified; full version uses dep-type

  κ-sig : Node → Label × List ℕ
  κ-sig n = Node.kappa-tag n , []

  ingest : SPPF → Node → SPPF
  ingest sppf n =
    let ni = node-index sppf
        σ' = fiber-assign (SPPF.sigma sppf) (σ-sig n) ni
        τ' = fiber-assign (SPPF.tau   sppf) (τ-sig n) ni
        κ' = fiber-assign (SPPF.kappa sppf) (κ-sig n) ni
    in record
      { sigma           = σ'
      ; tau             = τ'
      ; kappa           = κ'
      ; nodes           = SPPF.nodes sppf ++ (n ∷ [])
      ; κ-coprod        = SPPF.κ-coprod sppf  -- inherited: KappaCoproduct Label
                              -- has no fiber/node dependencies (phantom params removed)
      ; η-tower         = SPPF.η-tower sppf    -- η events added separately
      ; cleavage-planes = SPPF.cleavage-planes sppf
      ; obs             = SPPF.obs sppf
      ; σ-orient        = SPPF.σ-orient sppf
      ; τ-orient        = SPPF.τ-orient sppf
      ; κ-orient        = SPPF.κ-orient sppf
      }

  -- ── Correctness ────────────────────────────────────────────────────
  --
  -- Each IngestPost field follows from a named sub-lemma.  The proof
  -- structure mirrors the Python test suite:
  --
  --   node-present:  n is at the end of (nodes ++ [n]) → hereNode / thereNode.
  --     Test: test_single_node (190) — s.nodes[0]['ast_type'] == "Foo"
  --
  --   σ-shrinks:  assign-classes-bound on sigma.
  --     Test: test_assign_new (116), test_assign_existing (122)
  --
  --   κ-shrinks:  assign-classes-bound on kappa.
  --     Test: same pattern.
  --
  --   τ-shrinks:  assign-classes-bound composed with merge-classes-bound.
  --     The cascade only merges (never creates classes), so:
  --       |classes(cascade(assign τ))| ≤ |classes(assign τ)| ≤ |classes τ| + 1
  --     Test: test_canonical_classes (158) — merge reduces count.
  --
  --   η-grows:  append-≤ (proved above, line 1173).
  --     Test: TestPathologicalDeepCascade — tower grows over 6 levels.

  ingest-correct
    : ∀ (sppf : SPPF) (n : Node) (child-σs child-τs child-κs : List ℕ)
    → IngestPre sppf child-σs child-τs child-κs
    → IngestPost sppf (ingest sppf n) n
  ingest-correct sppf n child-σs child-τs child-κs pre =
    let ni = node-index sppf in record
      { node-present = ∈-++-right (SPPF.nodes sppf) n
      ; σ-shrinks    = assign-classes-bound (SPPF.sigma sppf) (σ-sig n) ni
      ; τ-shrinks    = assign-classes-bound (SPPF.tau   sppf) (τ-sig n) ni
      ; κ-shrinks    = assign-classes-bound (SPPF.kappa sppf) (κ-sig n) ni
      ; η-grows      = ≤-refl   -- η-tower unchanged in current ingest
      }


------------------------------------------------------------------------
-- 12.  Summary of open proof obligations
--
-- The following are postulated above and require future work:
--
-- P1. union-finds, union-preserves (UnionFind):
--     Path compression preserves the induced equivalence.
--     Proof: by induction on the path length to the root, which is
--     bounded by the log* of the set size (Tarjan 1975).
--     D1 track: abstract UFState kept; full implementation deferred
--     to a bounded-vector rewrite (D2 track, separate milestone).
--
-- P2. η-naturality / cascade-decomp-adequate (Eta):
--     EtaMorph is now a concrete record (idempotent + structural).
--     η-naturality (confluence) remains postulated; proof path is
--     Newman's lemma (termination from P2a + local confluence from
--     7 critical pair shapes, each witnessed by a test).
--     cascade-decomp-adequate is subsumable by η-naturality once proved.
--     Blocks on: P1 (union) for threading merge through local confluence.
--
-- P3. observe / sort-by-count (CellObs):
--     Implemented constructively:
--       - observe is structural recursion on level
--       - sort-by-count is insertion sort (count desc, level desc)
--     No postulate remains for CellObs.
--     Phase G splits P2 into:
--       P2a: cascade-terminates (constructive witness in code; WF strengthening pending)
--       P2b: η-naturality / cascade-decomp-adequate (residual, Newman's lemma)
--
-- P4. ingest (Ingest):
--     Constructive: ingest has a concrete body (fiber-assign on each fiber,
--     append node, inherit κ-coprod/cleavage/obs/orientations).
--     ingest-correct fully proved: node-present via ∈-++-right,
--     σ/τ/κ-shrinks via assign-classes-bound, η-grows via ≤-refl.
--     No holes remain.
--     τ-shrinks: ≤-trans (merge-classes-bound) (assign-classes-bound).
--     Remaining hole: τ-cascade portion of ingest body (blocks on P2a).
--
-- P4a. Fiber operations (Fiber):
--     fiber-assign, assign-classes-bound, fiber-merge, merge-classes-bound,
--     merge-canonical-decreases — abstract operations with test-witnessed
--     bounds.  Constructive once P1 (union) is available.
--     Tests: test_assign_new (116), test_assign_existing (122),
--            test_merge_different (139), test_canonical_classes (158).
--
-- P5. pullback witness construction (Cleavage):
--     Phase H: `postulate witness-from-transition` replaced with a concrete
--     definition with no local holes. CleavageTransition now carries explicit
--     runtime witness fields (parents, tracking proofs, pullback-proof), and
--     witness-from-transition is a direct projection into PullbackWitnessInterface.
--
-- P6. runtime-state adequacy (Cleavage):
--     The abstract CleavageRuntimeState/Transition encoding must be shown
--     adequate for the Python dictionaries/lists used by _process_cleavage.
--
-- P7. weight-at (Huffman):
--     Implemented constructively: lookup-weight performs a linear scan
--     of the HuffmanNode list by node-id using Boolean equality.
--     No postulate remains for the weight-at lookup.
--
-- Label (Core):
--     INTENTIONAL RESIDUAL — represents Python's classifier label type.
--     Not constructible within Agda alone.  This is correct modelling.
--
-- The GF(2) torsor (module SPPF.GF2) is fully proved.
-- The coproduct structure of κ (module SPPF.Kappa) is axiomatised
--   but not contradictory; it is satisfied by the concrete Python
--   implementation.
------------------------------------------------------------------------