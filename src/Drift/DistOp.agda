module Structures.DistOp where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

-- A unary “distinction operad” algebra: just an endomap U : A → A
record DistOpAlg (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    U       : Carrier → Carrier
open DistOpAlg public

-- Morphisms between (possibly different) universe levels
record HomAlg {ℓ₁ ℓ₂ : Level} (A : DistOpAlg ℓ₁) (B : DistOpAlg ℓ₂)
              : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    f   : Carrier A → Carrier B
    hom : ∀ x → f (U A x) ≡ U B (f x)
open HomAlg public

-- Initial algebra: (ℕ, suc)
NAlg : DistOpAlg lzero
NAlg .Carrier = ℕ
NAlg .U       = suc

-- Fold (primitive recursion) into any algebra
fold : ∀ {ℓ} (A : DistOpAlg ℓ) → Carrier A → ℕ → Carrier A
fold A a0 zero    = a0
fold A a0 (suc n) = U A (fold A a0 n)

-- The universal morphism from NAlg to A, given a seed a0 : A
mkFold : ∀ {ℓ} (A : DistOpAlg ℓ) (a0 : Carrier A) → HomAlg NAlg A
mkFold A a0 .f     = fold A a0
mkFold A a0 .hom n = refl   -- definitional: fold A a0 (suc n) ≡ U A (fold A a0 n)

-- Uniqueness of folds (initiality proof)
fold-uniq
  : ∀ {ℓ} (A : DistOpAlg ℓ) (a0 : Carrier A)
    (h : HomAlg NAlg A) → (f h zero ≡ a0)
    → ∀ n → f h n ≡ fold A a0 n
fold-uniq A a0 h f0 zero    = f0
fold-uniq A a0 h f0 (suc n) =
  -- f(suc n)  ≡⟨ hom h n ⟩  U (f n)  ≡⟨ cong (U A) (fold-uniq A a0 h f0 n) ⟩  U (fold A a0 n)
  -- … which is definitionally equal to fold A a0 (suc n)
  trans (hom h n) (cong (U A) (fold-uniq A a0 h f0 n))
