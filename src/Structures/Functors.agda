module Structures.Functors where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)   -- ≤-Konstruktoren
open import Data.Unit using (⊤; tt)

open import Structures.CutCat
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg
  ; plus; plus-hom; shiftHom; shift-id
  ; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg public

------------------------------------------------------------------------
-- difference from a ≤-witness, definitionally: diff (refl≤ m) ≡ 0
------------------------------------------------------------------------

diff : ∀ {m n} → m ≤ n → ℕ
diff {zero}   {n}     z≤n      = n
diff {suc m}  {suc n} (s≤s p)  = diff {m} {n} p

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
-- Functoriality
------------------------------------------------------------------------

-- Identity: since diff (refl≤ m) reduces to 0, shift-id applies
F-id : ∀ {m} n → (F-arr (refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id n = shift-id n

-- Composition: reduces if _∘Alg_ composes shifts additively
F-comp :
  ∀ {a b c} (g : b ≤ c) (f : a ≤ b) n →
    (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (g ∙ f)) .f n
F-comp g f n = refl
