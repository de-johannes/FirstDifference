module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-suc; ≤-refl; ≤-trans; ≤-irrelevant)

-- Import our enhanced structures with consistent Data.Nat.≤ usage
open import Structures.CutCat using (Category; CutCat)
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg; plus; plus-hom; shiftHom; shift-id; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg     public

------------------------------------------------------------------------
-- Semantic Time Functor: CutCat → DistOpAlg
-- Now using standard Data.Nat.≤ throughout - no conversion needed!
------------------------------------------------------------------------

-- Difference function: extracts temporal progression amount from ≤ proof
diff : ∀ {m n} → m ≤ n → ℕ
diff {zero}   {n}     _  = n         -- zero ≤ n gives difference n
diff {suc m}  {zero}  () 
diff {suc m}  {suc n} p  = diff (Data.Nat.Properties.≤-pred p)

-- Key lemma: diff of reflexivity is always zero
diff-refl : ∀ m → diff (≤-refl {m}) ≡ zero
diff-refl zero    = refl
diff-refl (suc m) = diff-refl m

-- Semantic interpretation: temporal progression ≤ proof gives arithmetic gap
end-eq : ∀ {b c} (g : b ≤ c) → b + diff g ≡ c
end-eq {zero}   {c}     _  = +-identityˡ c
end-eq {suc b}  {zero}  ()
end-eq {suc b}  {suc c} p  = cong suc (end-eq (Data.Nat.Properties.≤-pred p))

-- Composition preserves temporal arithmetic
diff-∙ : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) → diff (≤-trans f g) ≡ diff f + diff g
diff-∙ {zero}   {b} {c}  _ g = trans refl (sym (end-eq g))
diff-∙ {suc a}  {zero}  () _
diff-∙ {suc a}  {suc b} {zero}  _ ()
diff-∙ {suc a}  {suc b} {suc c} f g = diff-∙ (Data.Nat.Properties.≤-pred f) (Data.Nat.Properties.≤-pred g)

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
-- Functoriality proofs: respects category structure
------------------------------------------------------------------------

-- Identity preservation: reflexive temporal relation maps to identity shift
F-id : ∀ {m} n → (F-arr ≤-refl) .f n ≡ (idAlg (F-obj m)) .f n
F-id {m} n rewrite diff-refl m = shift-id n

-- Composition preservation: temporal composition maps to arithmetic composition
F-comp : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) (n : ℕ) →
         (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (≤-trans f g)) .f n
F-comp f g n
  rewrite +-assoc n (diff f) (diff g)
        | sym (diff-∙ f g) = refl

------------------------------------------------------------------------
-- Beautiful: No type conversions, everything uses Data.Nat.≤ consistently!
------------------------------------------------------------------------
