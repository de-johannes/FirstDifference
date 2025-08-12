module Structures.Functors where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-suc)
open import Data.Unit using (⊤; tt)

-- Sauberer Import: nur qualified, dann selective opens
import Structures.CutCat as C
open C using (_≤_; refl≤; z≤n; s≤s; _∙_)

open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg
  ; plus; plus-hom; shiftHom; shift-id
  ; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg     public

------------------------------------------------------------------------
-- Difference from a ≤-witness: returns n − m
------------------------------------------------------------------------

diff : ∀ {m n} → m ≤ n → ℕ
diff {zero}   {n}     z≤n      = n
diff {suc m}  {suc n} (s≤s p)  = diff {m} {n} p

-- Helper: "walking" the witness adds exactly its length
end-eq : ∀ {b c} (g : b ≤ c) → b + diff g ≡ c
end-eq {zero}   {c}     z≤n     = +-identityˡ c
end-eq {suc b}  {suc c} (s≤s g) = 
  -- suc b + diff (s≤s g) = suc b + diff g = suc (b + diff g) ≡ suc c
  cong suc (end-eq g)

-- Composition law for diff
diff-∙ : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) → diff (f ∙ g) ≡ diff f + diff g
diff-∙ {zero}   {b} {c}  z≤n      g =            
  trans refl (sym (end-eq g))
diff-∙ {suc a} {suc b} {suc c} (s≤s f) (s≤s g) =
  diff-∙ f g

------------------------------------------------------------------------
-- Functor CutCat → DistOpAlg  (Semantic Time)
------------------------------------------------------------------------

F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m ≤ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

-- object mapping (for explicit reference)
semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality
------------------------------------------------------------------------

-- Identity: diff (refl≤ m) reduces to 0, hence shift-id applies pointwise
F-id : ∀ {m} n → (F-arr (refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id n = shift-id n

-- Composition
F-comp :
  ∀ {a b c} (f : a ≤ b) (g : b ≤ c) (n : ℕ) →
    (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (f ∙ g)) .f n
F-comp f g n
  rewrite +-assoc n (diff f) (diff g)
        | sym (diff-∙ f g) = refl 
