------------------------------------------------------------------------
-- CSTZ.Exterior.Boundary
--
-- The boundary operator ∂ on Λ(GF(2)^n) and the chain complex
-- property ∂ ∘ ∂ = 0.
--
-- Paper §5, Def 5.3-5.4:
--   ∂(e_{i₁} ∧ ⋯ ∧ e_{iₖ}) = Σⱼ e_{i₁} ∧ ⋯ ∧ ê_{iⱼ} ∧ ⋯ ∧ e_{iₖ}
--
-- Paper §5, Prop 5.5:
--   ∂ ∘ ∂ = 0 because each (k-2)-cell appears exactly twice.
--   Over GF(2), 1+1=0.
--
-- Implementation:
--   ∂(f)(T) = Σᵢ [T[i] = false] · f(T ∪ {i})
--
-- That is: to compute the boundary of f at subset T, sum over all
-- positions i NOT in T, and look up f on the subset T ∪ {i}.
-- Removing element i from a k-subset S gives the (k-1)-subset S\{i},
-- which equals T when T = S\{i}, i.e., S = T∪{i} and i∉T.
------------------------------------------------------------------------

module CSTZ.Exterior.Boundary where

open import CSTZ.GF2
open import CSTZ.GF2.Properties
open import CSTZ.Exterior.Basis

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; _[_]≔_)
open import Data.Bool.Base using (if_then_else_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Contribution of position i to the boundary

-- contrib i f T = f(T ∪ {i})  if i ∉ T  (i.e., T[i] = false)
--               = 0            if i ∈ T
private
  contrib : ∀ {n} → Fin n → Exterior n → Subset n → F
  contrib i f t with lookup t i
  ... | true  = 𝟘
  ... | false = f (t [ i ]≔ true)

------------------------------------------------------------------------
-- Boundary operator: ∂(f)(T) = Σᵢ contrib i f T

-- We fold over positions using the Fin n structure directly.
-- ∂-aux m f t = Σ_{i=0}^{m-1} contrib (inject i) f t
-- where inject maps i from Fin m to Fin n.

∂ : ∀ {n} → Exterior n → Exterior n
∂ {n} f t = go n (λ m p → Data.Fin.fromℕ< p) f t
  where
    open import Data.Nat using (_<_ ; _≤_ ; z≤n ; s≤s)
    open import Data.Nat.Properties using (≤-refl ; m≤n⇒m≤1+n)

    go : ∀ {n} (m : ℕ) → (∀ k → suc k ≤ m → Fin n) → Exterior n → Subset n → F
    go zero    _   _ _ = 𝟘
    go (suc m) inj f t =
      contrib (inj m ≤-refl) f t +F go m (λ k p → inj k (m≤n⇒m≤1+n p)) f t

-- Specialize: for ∂ on Exterior n, we fold i from 0 to n-1.
-- The `go` above does this when called with m = n and inj = fromℕ<.

------------------------------------------------------------------------
-- ∂ ∘ ∂ = 0
--
-- Paper §5, Prop 5.5.
--
-- Proof:
--   ∂(∂(f))(T) = Σᵢ [T[i]=0] · ∂(f)(T∪{i})
--              = Σᵢ [T[i]=0] · Σⱼ [(T∪{i})[j]=0] · f(T∪{i}∪{j})
--
-- Case i = j:  (T∪{i})[i] = true, so the inner contributes 0.
-- Case i ≠ j, both ∉ T:
--   f(T∪{i,j}) appears once from outer=i,inner=j
--                    and once from outer=j,inner=i.
--   Over GF(2), 1 + 1 = 0.  QED.
--
-- The formal proof proceeds by showing the double sum is equal to
-- 0 via the pairing argument.  This is the hardest proof in Phase 1.

-- Python cofibration (STUDY.md §8.1, P4):
--   * Basis sweep:  src/cstz/verification.py :: check_boundary_squared
--   * Full exhaustion at n=3 (all 2^(2^n) elements):
--                   src/cstz/verification.py :: check_boundary_squared_all
--   Under operationalism, exhaustion at fixed n is a proof at that n
--   — Python covers n ≤ 3 concretely; the uniform-in-n proof below is
--   the Agda side's contribution.
postulate
  ∂∘∂≡0 : ∀ {n} (f : Exterior n) (t : Subset n) → ∂ (∂ f) t ≡ 𝟘
-- Proof obligation: combinatorial pairing argument.
-- Each pair (i,j) with i≠j, i∉T, j∉T contributes f(T∪{i,j}) twice.
-- Over GF(2), double-cancel kills each pair.
-- To be mechanized: requires showing the sum decomposes into
-- paired terms, each of which cancels via double-cancel.
