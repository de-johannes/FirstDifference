module Structures.Functors where

-- Functor CutCat ⟶ DistOpAlg: “semantic time”.
-- On objects: every Xₙ ↦ NAlg. On arrows m≤n ↦ shift by diff(m,n).

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)

-- Our custom structures
import Structures.CutCat as CC
import Structures.DistOpOperad as DO

------------------------------------------------------------------------
-- Compute the “gap” diff : m≤n ↦ (n − m) structurally
------------------------------------------------------------------------

diff : ∀ {m n} → CC._≤_ m n → ℕ
diff {m} {n} p = go m n p
  where
    go : ∀ m n → CC._≤_ m n → ℕ
    go zero     n        CC.z≤n       = n
    go (suc m′) (suc n′) (CC.s≤s p′)  = go m′ n′ p′

-- Identity gap is 0
diff-refl : ∀ m → diff (CC.refl≤ m) ≡ 0
diff-refl zero    = refl
diff-refl (suc m) = diff-refl m

-- Composition of gaps is addition
diff-comp :
  ∀ {a b c} (f : CC._≤_ a b) (g : CC._≤_ b c) →
  diff (f CC._∙ᴄ_ g) ≡ diff f + diff g
diff-comp CC.z≤n       g             = refl
diff-comp (CC.s≤s f) (CC.s≤s g)      = cong suc (diff-comp f g)

------------------------------------------------------------------------
-- The functor on objects and arrows
------------------------------------------------------------------------

F-obj : ℕ → DO.DistOpAlg lzero
F-obj _ = DO.NAlg

F-arr : ∀ {m n} → CC._≤_ m n → DO.HomAlg (F-obj m) (F-obj n)
F-arr p = DO.shiftHom (diff p)          -- shift by the computed gap

-- A tiny helper to apply a HomAlg to a value
apply : ∀ {A B} → DO.HomAlg A B → DO.Carrier A → DO.Carrier B
apply h = DO.f h

------------------------------------------------------------------------
-- Functoriality proofs
------------------------------------------------------------------------

-- Identity: diff (refl≤ m) = 0  ⇒  shiftHom 0 = idAlg
F-id : ∀ {m} (n : ℕ) →
  apply (F-arr (CC.refl≤ m)) n ≡ apply (DO.idAlg (F-obj m)) n
F-id {m} n =                         -- rewrite shift amount to 0 then use DO.lemma
  trans (cong (λ k → DO.plus k n) (diff-refl m)) (DO.shift-id n)

-- Composition: diff (f∙ᴄ g) = diff f + diff g  ⇒  shifts compose additively
F-comp :
  ∀ {a b c} (f : CC._≤_ a b) (g : CC._≤_ b c) (n : ℕ) →
    apply (DO._∘Alg_ (F-arr g) (F-arr f)) n ≡ apply (F-arr (f CC._∙ᴄ_ g)) n
F-comp f g n =
  trans (DO.shift-comp n (diff f) (diff g))
       (cong (λ k → DO.plus k n) (sym (diff-comp f g)))
