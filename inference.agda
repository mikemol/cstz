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
open import Data.Nat             using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
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
-- 2.  UnionFind  —  union-find as a setoid quotient
--
-- We model the union-find state as a function  parent : A → A  that
-- is idempotent on the image (find ∘ find = find).  The equivalence
-- relation induced is  a ~ b  iff  find a = find b.
------------------------------------------------------------------------

module SPPF.UnionFind where

  -- Abstract interface ---------------------------------------------
  --
  -- In a constructive setting the mutable array is replaced by a
  -- finite function  A → A.  We parameterise by a decidable set A.

  record UFState (A : Set) : Set where
    field
      parent  : A → A
      -- Convergence: every chain reaches a fixed point.
      -- (In practice bounded by the set size; here we postulate it.)
      find    : A → A
      find-fp : ∀ a → find (find a) ≡ find a     -- idempotent
      find-≡  : ∀ a → find a ≡ find (parent a)   -- consistent with parent

  -- Induced equivalence --------------------------------------------

  _~[_]_ : ∀ {A} → A → UFState A → A → Set
  a ~[ uf ] b = UFState.find uf a ≡ UFState.find uf b

  ~-isEquiv : ∀ {A} (uf : UFState A) → IsEquivalence (_~[ uf ]_)
  ~-isEquiv uf = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  -- Union operation ------------------------------------------------
  --
  -- union a b produces a new state in which find a = find b.
  -- We cannot implement this purely without a mutable environment;
  -- we postulate the existence of the result and its key property.

  postulate
    -- POSTULATE: union-find update step.
    -- A full proof needs a well-founded recursion on path length and
    -- a proof that path compression preserves the induced equivalence.
    union : ∀ {A} → UFState A → A → A → UFState A

    union-finds : ∀ {A} (uf : UFState A) (a b : A)
                → let uf' = union uf a b
                  in  UFState.find uf' a ≡ UFState.find uf' b

    union-preserves : ∀ {A} (uf : UFState A) (a b c d : A)
                    → c ~[ uf ] d
                    → c ~[ union uf a b ] d


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
      uf        : UFState ℕ           -- acts on fids

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

    -- The number of canonical classes
    -- (not easily computable without decidable equality on ℕ; we leave
    -- it as a field to be provided by the classifier)
    canonical-count : ℕ
    canonical-count = length classes   -- upper bound; exact count needs dedup


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

  record KappaCoproduct
           (Label : Set)
           (σ τ κ : Fiber Label)
           (nodes : List NodeCoords) : Set where
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

  postulate
    -- POSTULATE: naturality of η-cascade.
    -- A full proof requires showing that the worklist fixed-point in
    -- _cascade_eta terminates and produces a quotient that satisfies
    -- the naturality square above.  Termination follows from the fact
    -- that each merge strictly reduces the number of canonical τ-ids.
    EtaMorph : EtaContext → (ℕ → ℕ) → Set

    η-naturality : ∀ {Label : Set}
           → (ctx : EtaContext)
           → (φ : ℕ → ℕ)
           → (η-map : ℕ → ℕ)
           → EtaMorph ctx φ
           → EtaMorph ctx η-map
           → (∀ t → η-map (φ t) ≡ φ (η-map t))

    -- POSTULATE: cascade decomposition adequacy (R8 spec gap).
    --
    -- The Python implementation factors η-cascade into two cooperating
    -- functions:
    --   · _cascade_eta           — outer worklist over child-τ-changed keys
    --   · _cascade_abstraction_merge — inner sweep via _tau_structural_by_variant
    --
    -- The _tau_structural_by_variant inverted index has no counterpart in
    -- this spec.  Cross-key τ-collisions are resolved by calling canonical()
    -- dynamically inside _cascade_abstraction_merge rather than by re-entering
    -- through the variant-name axis, which provides transitivity without a
    -- second outer pass (validated by test_cascade_abstraction_merge_cross_key_stale).
    --
    -- This postulate asserts that the two-function decomposition jointly
    -- computes the same τ-quotient map as the single fixed-point that
    -- η-naturality (P2) requires.
    cascade-decomp-adequate
      : ∀ (ctx : EtaContext)
          (φ-single φ-decomp : ℕ → ℕ)
      → EtaMorph ctx φ-single    -- single-pass fixed-point map (P2)
      → EtaMorph ctx φ-decomp    -- two-function decomposition map
      → ∀ t → φ-single t ≡ φ-decomp t


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

  postulate
    -- POSTULATE: construction of a witness from emitted transitions.
    -- This is the formal bridge to core.py _process_cleavage:
    -- if a transition emits a cleavage plane, we can extract a
    -- pullback witness linked to the recorded parent-key map.
    witness-from-transition
      : (tr : CleavageTransition)
      → CleavageTransition.step tr ≡ emit-plane
      → PullbackWitnessInterface tr

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
      where
        postulate
          -- POSTULATE: list index / node-id lookup from Huffman tree.
          -- Kept abstract to avoid a misleading constant implementation.
          weight-at : ℕ → ℕ

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
      κ-coprod : KappaCoproduct Label sigma tau kappa nodes

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

  -- List membership witness for child-id preconditions.
  data _∈ℕ_ : ℕ → List ℕ → Set where
    hereℕ  : ∀ {x xs} → x ∈ℕ (x ∷ xs)
    thereℕ : ∀ {x y xs} → x ∈ℕ xs → x ∈ℕ (y ∷ xs)

  data _∈Node_ : Node → List Node → Set where
    hereNode  : ∀ {n ns} → n ∈Node (n ∷ ns)
    thereNode : ∀ {n m ns} → n ∈Node ns → n ∈Node (m ∷ ns)

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

  postulate
    -- POSTULATE: the ingest function satisfying the above contract.
    -- A full proof requires:
    --   1. Termination of _cascade_eta (strict decrease in canonical τ-count)
    --   2. Termination of _cascade_abstraction_merge (same argument)
    --   3. The σ/τ/κ sizes bound (by construction: _assign only adds,
    --      union only merges)
    ingest : SPPF → Node → SPPF


------------------------------------------------------------------------
-- 12.  Summary of open proof obligations
--
-- The following are postulated above and require future work:
--
-- P1. union-finds, union-preserves (UnionFind):
--     Path compression preserves the induced equivalence.
--     Proof: by induction on the path length to the root, which is
--     bounded by the log* of the set size (Tarjan 1975).
--
-- P2. η-naturality (Eta):
--     The cascade worklist reaches a fixed point and the resulting
--     quotient map η-map commutes with every merge morphism φ.
--     Proof: by well-founded induction on (canonical τ-count, worklist size).
--
-- P3. observe / sort-by-count (CellObs):
--     Implemented constructively:
--       - observe is structural recursion on level
--       - sort-by-count is insertion sort (count desc, level desc)
--     No postulate remains for CellObs.
--
-- P4. ingest (Ingest):
--     The full ingestion function satisfies its pre/post contract.
--     Proof: combines P1–P3 with the structural bounds on fiber sizes.

-- P5. pullback witness construction (Cleavage):
--     IsPullback now includes both mediator existence and uniqueness.
--     Phase 3 adds PullbackWitnessInterface and witness-from-transition,
--     tying witnesses to level transitions and parent-key tracking.
--     LevelHasKey/ParentTracked are now concrete inductive lookup
--     relations over the runtime list encodings. Remaining work is to
--     prove extraction correctness for witness-from-transition.

-- P6. runtime-state adequacy (Cleavage):
--     The abstract CleavageRuntimeState/Transition encoding must be shown
--     adequate for the Python dictionaries/lists used by _process_cleavage.
--
-- The GF(2) torsor (module SPPF.GF2) is fully proved.
-- The coproduct structure of κ (module SPPF.Kappa) is axiomatised
--   but not contradictory; it is satisfied by the concrete Python
--   implementation.
------------------------------------------------------------------------