module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-suc)

-- Import our enhanced structures
import Structures.CutCat as C
open C using (_≤_; refl≤; z≤n; s≤s; _∙_)
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg; plus; plus-hom; shiftHom; shift-id; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg     public

------------------------------------------------------------------------
-- Semantic Time Functor: CutCat → DistOpAlg
-- This captures the essential bridge from temporal stages to arithmetic
------------------------------------------------------------------------

-- Difference function: extracts temporal progression amount
diff : ∀ {m n} → m ≤ n → ℕ
diff {zero}   {n}     z≤n      = n
diff {suc m}  {suc n} (s≤s p)  = diff {m} {n} p

-- Key lemma: diff of reflexivity is always zero (temporal self-relation)
diff-refl : ∀ m → diff (refl≤ m) ≡ zero
diff-refl zero    = refl  -- diff z≤n = zero by definition
diff-refl (suc m) = diff-refl m  -- diff (s≤s (refl≤ m)) = diff (refl≤ m)

-- Semantic interpretation: temporal progression ≤ proof gives arithmetic gap
end-eq : ∀ {b c} (g : b ≤ c) → b + diff g ≡ c
end-eq {zero}   {c}     z≤n     = +-identityˡ c
end-eq {suc b}  {suc c} (s≤s g) = cong suc (end-eq g)

-- Composition preserves temporal arithmetic
diff-∙ : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) → diff (f ∙ g) ≡ diff f + diff g
diff-∙ {zero}   {b} {c}  z≤n      g = trans refl (sym (end-eq g))
diff-∙ {suc a} {suc b} {suc c} (s≤s f) (s≤s g) = diff-∙ f g

------------------------------------------------------------------------
-- Semantic Time Functor: The conceptual bridge
------------------------------------------------------------------------

-- All temporal stages map to the same algebra: natural numbers with successor
F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

-- Temporal progression maps to arithmetic shift by progression amount
F-arr : ∀ {m n} → m ≤ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

-- Semantic interpretation: stage number as natural number
semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality proofs: Semantic Time Functor respects category structure
------------------------------------------------------------------------

-- Identity preservation: reflexive temporal relation maps to identity shift
F-id : ∀ {m} n → (F-arr (refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id {m} n rewrite diff-refl m = shift-id n

-- Composition preservation: temporal composition maps to arithmetic composition
F-comp : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) (n : ℕ) →
         (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (f ∙ g)) .f n
F-comp f g n
  rewrite +-assoc n (diff f) (diff g)
        | sym (diff-∙ f g) = refl

------------------------------------------------------------------------
-- Conceptual summary:
-- This functor captures the essence of how temporal progression
-- (tracked by semantic time in drift histories) translates to
-- arithmetic structure (natural numbers with successor operation)
------------------------------------------------------------------------
