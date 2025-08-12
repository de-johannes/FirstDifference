module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-suc)

-- Back to our domain-optimized CutCat!
import Structures.CutCat as C
open C using (_≤_; refl≤; z≤n; s≤s; _∙_)
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg; plus; plus-hom; shiftHom; shift-id; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg     public

------------------------------------------------------------------------
-- Semantic Time Functor: Beautiful and clean again!
------------------------------------------------------------------------

-- Difference function: clean pattern matching on our custom ≤
diff : ∀ {m n} → m ≤ n → ℕ
diff {zero}   {n}     z≤n      = n
diff {suc m}  {suc n} (s≤s p)  = diff {m} {n} p

-- Key lemma: diff of reflexivity is definitionally zero!
diff-refl : ∀ m → diff (refl≤ m) ≡ zero
diff-refl zero    = refl  -- z≤n case: diff z≤n = zero
diff-refl (suc m) = diff-refl m  -- s≤s case: diff (s≤s (refl≤ m)) = diff (refl≤ m)

-- Semantic interpretation: clean and direct
end-eq : ∀ {b c} (g : b ≤ c) → b + diff g ≡ c
end-eq {zero}   {c}     z≤n     = +-identityˡ c
end-eq {suc b}  {suc c} (s≤s g) = cong suc (end-eq g)

-- Composition: elegant proof
diff-∙ : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) → diff (f ∙ g) ≡ diff f + diff g
diff-∙ {zero}   {b} {c}  z≤n      g = trans refl (sym (end-eq g))
diff-∙ {suc a} {suc b} {suc c} (s≤s f) (s≤s g) = diff-∙ f g

------------------------------------------------------------------------
-- The Functor: CutCat → DistOpAlg
------------------------------------------------------------------------

F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m ≤ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality: Clean proofs!
------------------------------------------------------------------------

F-id : ∀ {m} n → (F-arr (refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id {m} n rewrite diff-refl m = shift-id n

F-comp : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) (n : ℕ) →
         (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (f ∙ g)) .f n
F-comp f g n
  rewrite +-assoc n (diff f) (diff g)
        | sym (diff-∙ f g) = refl

------------------------------------------------------------------------
-- This is how domain-specific design should work: 
-- Custom definitions optimized for the problem domain!
------------------------------------------------------------------------
