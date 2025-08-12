module Structures.Functors where

-- This module formalises "semantic time" T(n) from Part I of the Backbone PDF.
-- Semantic time counts irreducible drift events and maps them to ℕ via the initial
-- algebra (NAlg, suc) as a functor: CutCat ⟶ DistOpAlg.

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)

open import Structures.CutCat
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg
  ; plus; plus-hom; shiftHom; shift-id
  ; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg public

------------------------------------------------------------------------
-- Arithmetic difference computed from the ≤-witness (no monus!)
------------------------------------------------------------------------

diff : ∀ {m n} → m ≤ n → ℕ
diff {m} {n} (refl≤ .m) = 0
diff (s≤s p)            = suc (diff p)

------------------------------------------------------------------------
-- Functor CutCat → DistOpAlg  (Semantic Time)
------------------------------------------------------------------------

F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m ≤ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

-- object mapping, for reference
semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality proofs
------------------------------------------------------------------------

-- Identity: now definitional, since diff (refl≤ m) reduces to 0
F-id : ∀ {m} n → (F-arr (refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id n = shift-id n

-- Composition: reduces by definitions of diff and shift composition
F-comp :
  ∀ {a b c} (g : b ≤ c) (f : a ≤ b) n →
    (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (g ∙ f)) .f n
F-comp g f n = refl
