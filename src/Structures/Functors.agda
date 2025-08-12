module Structures.Functors where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)

open import Structures.CutCat
open import Structures.DistOpOperad

-- Difference (n - m) from a ≤-witness, used to build "+k".
diff : ∀ {m n} → m ≤ n → ℕ
diff z≤n       = zero
diff (s≤s p)   = suc (diff p)

-- Addition-by-k is a (ℕ,succ)-endomorphism and a homomorphism.
plus : ℕ → ℕ → ℕ
plus k n = n + k

plus-hom : ∀ k n → plus k (suc n) ≡ suc (plus k n)
plus-hom k n = refl   -- by definition of _+_ in stdlib

-- Turn “+k” into a HomAlg NAlg NAlg
shiftHom : ℕ → HomAlg NAlg NAlg
shiftHom k .f     = plus k
shiftHom k .hom n = plus-hom k n

-- Composition law: +k₂ ∘ +k₁ = +(k₁ + k₂)
shift-comp : ∀ k₁ k₂ n → plus k₂ (plus k₁ n) ≡ plus (k₁ + k₂) n
shift-comp k₁ k₂ n = refl

-- Identity: +0
shift-id : ∀ n → plus 0 n ≡ n
shift-id n = refl

-- The functor on objects is constant to NAlg (time-indexed states share carrier ℕ).
-- On arrows u_{m,n} (a ≤-witness) we send to the endomorphism “+ (n−m)”.
F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m ≤ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

-- Functoriality proofs
F-id : ∀ {m} → (F-arr (refl≤ m)) .f ≡ (idAlg (F-obj m)) .f
F-id = refl   -- diff (refl≤ m) = 0, both functions reduce definitionally to id

F-comp
  : ∀ {a b c} (g : b ≤ c) (f : a ≤ b)
  → ( _∘Alg_ (F-arr g) (F-arr f) ) .f ≡ (F-arr (g ∙ f)) .f
F-comp g f = refl
-- since (diff (g ∙ f)) = diff f + diff g and function bodies are definitional +k
