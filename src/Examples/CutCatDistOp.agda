module Example.CutCatDistOp where

open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

U : ℕ → ℕ
U = suc

-- "Square commutes" here reduces to suc ∘ id ≡ id ∘ suc, i.e. refl.
square-comm : (k : ℕ) → U k ≡ U k
square-comm k = refl
