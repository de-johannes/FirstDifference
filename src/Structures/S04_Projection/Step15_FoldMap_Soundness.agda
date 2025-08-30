{-# OPTIONS --safe #-}

-- Step 15: FoldMap – basic algebraic soundness lemmas
-- Key identity: popcount (drift a b) ≡ andCount a b

module Structures.S04_Projection.Step15_FoldMap_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)

open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool; _∧_)
open import Structures.S01_BooleanCore.Step02_VectorOperations  using (Dist; drift)
open import Structures.S04_Projection.Step15_FoldMap
  using (toℕ; popcount; andCount)

-- Helper: push congruence through (+) on the right
cong-+ʳ : ∀ {m n} → m ≡ n → ∀ k → m + k ≡ n + k
cong-+ʳ refl k = refl

-- Main identity: componentwise-AND counted equals count of ANDed vector
popcount-drift≡andCount : ∀ {n} (a b : Dist n) → popcount (drift a b) ≡ andCount a b
popcount-drift≡andCount {zero}  []       []       = refl
popcount-drift≡andCount {suc n} (x ∷ xs) (y ∷ ys) =
  -- LHS = toℕ (x ∧ y) + popcount (drift xs ys)
  -- RHS = toℕ (x ∧ y) + andCount xs ys
  cong-+ʳ (popcount-drift≡andCount xs ys) (toℕ (x ∧ y))