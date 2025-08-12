module Structures.Functors where

-- This module formalises "semantic time" T(n) from Part I of the Backbone PDF.
-- Semantic time counts irreducible drift events and maps them to ℕ via the initial
-- algebra (NAlg, suc).

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)

open import Structures.CutCat
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg
  ; plus; plus-hom; shiftHom
  ; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg public

------------------------------------------------------------------------
-- Difference (n - m) from a ≤-witness
------------------------------------------------------------------------

diff : ∀ {m n} → m ≤ n → ℕ
diff z≤n     = zero
diff (s≤s p) = suc (diff p)

------------------------------------------------------------------------
-- Local definition: identity shift (+0)
------------------------------------------------------------------------

shift-id : ∀ n → plus 0 n ≡ n
shift-id n = refl

------------------------------------------------------------------------
-- Functor CutCat → DistOpAlg  (Semantic Time)
------------------------------------------------------------------------

F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m ≤ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality proofs
------------------------------------------------------------------------

F-id : ∀ {m} n → (F-arr (refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id n = shift-id n

F-comp :
  ∀ {a b c} (g : b ≤ c) (f : a ≤ b) n →
    (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (g ∙ f)) .f n
F-comp g f n = refl
