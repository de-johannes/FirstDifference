module Structures.Functors where

-- This module formalises "semantic time" T(n), as defined in the Backbone of History (2025).
-- Semantic time counts irreducible distinction events via the canonical functor:
--   CutCat ⟶ DistOpAlg
-- mapping temporal steps to the initial algebra (ℕ, succ).

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)

open import Structures.CutCat
open import Structures.DistOpOperad using (DistOpAlg; HomAlg; NAlg; plus; plus-hom; shiftHom; idAlg; _∘Alg_)
open DistOpAlg public
open HomAlg public

------------------------------------------------------------------------
-- Difference (n − m) from a ≤-witness
------------------------------------------------------------------------

diff : ∀ {m n} → m ≤ n → ℕ
diff z≤n     = zero
diff (s≤s p) = suc (diff p)

------------------------------------------------------------------------
-- Semantic time functor CutCat → DistOpAlg
-- Objects are always mapped to (ℕ, succ) = NAlg.
-- Arrows u_{m,n} : m ≤ n are mapped to shiftHom (n − m)
------------------------------------------------------------------------

F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m ≤ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

------------------------------------------------------------------------
-- Semantic Time (object part only): n ↦ ℕ, representing state after n distinctions
------------------------------------------------------------------------

semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality (minimal categorical laws)
------------------------------------------------------------------------

F-id : ∀ {m} → (F-arr (refl≤ m)) .f ≡ (idAlg (F-obj m)) .f
F-id = refl  -- diff (refl≤ m) = 0 → shiftHom 0 = identity

F-comp :
  ∀ {a b c} (g : b ≤ c) (f : a ≤ b) →
    (_∘Alg_ (F-arr g) (F-arr f)) .f ≡ (F-arr (g ∙ f)) .f
F-comp g f = refl
-- diff (g ∙ f) = diff f + diff g; shiftHom distributes over + definitionally
