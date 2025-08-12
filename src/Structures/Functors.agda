module Structures.Functors where

-- This module formalises "semantic time" T(n) from Part I of the Backbone PDF.
-- Semantic time counts irreducible drift events and maps them to ℕ via the initial
-- algebra (NAlg, suc) as a functor: CutCat ⟶ DistOpAlg.

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _-_)
open import Data.Unit using (⊤; tt)

open import Structures.CutCat
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg
  ; plus; plus-hom; shiftHom; shift-id
  ; idAlg; _∘Alg_ )

-- Bring record fields into scope
open DistOpAlg public
open HomAlg public

------------------------------------------------------------------------
-- Arithmetic definition: difference (n - m) from a ≤-witness
------------------------------------------------------------------------

diff : ∀ {m n} → m ≤ n → ℕ
diff {m} {n} _ = n - m   -- use standard library subtraction

------------------------------------------------------------------------
-- Functor CutCat → DistOpAlg  (Semantic Time)
------------------------------------------------------------------------

F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m ≤ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

-- Semantic time as object mapping only (for explicit reference in code/docs)
semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality proofs
------------------------------------------------------------------------

-- Identity: diff (refl≤ m) = 0, so shiftHom 0 = id
F-id : ∀ {m} n → (F-arr (refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id n = shift-id n

-- Composition: diff (g ∙ f) = diff f + diff g definitionally
F-comp :
  ∀ {a b c} (g : b ≤ c) (f : a ≤ b) n →
    (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (g ∙ f)) .f n
F-comp g f n = refl
