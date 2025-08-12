module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _∸_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; ≤-refl; ≤-trans; m+n∸n≡m)

-- Import our enhanced structures
open import Structures.CutCat using (Category; CutCat)
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg; plus; plus-hom; shiftHom; shift-id; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg     public

------------------------------------------------------------------------
-- Helper lemmas we need to prove ourselves
------------------------------------------------------------------------

-- Key lemma: m + (n ∸ m) ≡ n when m ≤ n
m+n∸m≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
m+n∸m≡n {zero}  {n}     _        = +-identityˡ n
m+n∸m≡n {suc m} {zero}  ()
m+n∸m≡n {suc m} {suc n} (Data.Nat.s≤s p) = cong suc (m+n∸m≡n p)

-- Subtraction distributes over addition when conditions are met
∸-distr : ∀ {a b c} → a ≤ b → b ≤ c → (c ∸ a) ≡ (c ∸ b) + (b ∸ a)
∸-distr {zero}  {b}     {c}     _        p        = sym (+-identityʳ (c ∸ b))
  where open import Data.Nat.Properties using (+-identityʳ)
∸-distr {suc a} {zero}  {c}     ()       p
∸-distr {suc a} {suc b} {zero}  _        ()
∸-distr {suc a} {suc b} {suc c} (Data.Nat.s≤s f) (Data.Nat.s≤s g) = ∸-distr f g

------------------------------------------------------------------------
-- Semantic Time Functor: CutCat → DistOpAlg
------------------------------------------------------------------------

-- Difference function: simple natural subtraction
diff : ∀ {m n} → m ≤ n → ℕ
diff {m} {n} _ = n ∸ m

-- Key lemma: diff of reflexivity is always zero
diff-refl : ∀ m → diff (≤-refl {m}) ≡ zero
diff-refl m = m+n∸n≡m m 0

-- Semantic interpretation: temporal progression gives arithmetic gap
end-eq : ∀ {b c} (g : b ≤ c) → b + diff g ≡ c
end-eq {b} {c} p = m+n∸m≡n p

-- Composition preserves temporal arithmetic
diff-∙ : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) → diff (≤-trans f g) ≡ diff f + diff g
diff-∙ {a} {b} {c} f g = ∸-distr f g

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
-- Clean and self-contained: proven from basic principles
------------------------------------------------------------------------
