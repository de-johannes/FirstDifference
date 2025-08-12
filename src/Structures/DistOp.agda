module Structures.DistOp where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Nat            using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

-- DistOp-algebra: carrier with a single endomorphism U
record DistOpAlg (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    U       : Carrier → Carrier
open DistOpAlg public

-- Morphisms of algebras: f ∘ U_A = U_B ∘ f (pointwise)
record HomAlg {ℓ} (A B : DistOpAlg ℓ) : Set (lsuc ℓ) where
  field
    f   : Carrier A → Carrier B
    hom : ∀ x → f (U A x) ≡ U B (f x)
open HomAlg public

-- Initial algebra: (ℕ, suc)
NAlg : DistOpAlg lzero
NAlg .Carrier = ℕ
NAlg .U       = suc

-- fold: given an algebra (A,U) and a chosen a0 : A, build ℕ → A by primitive recursion
fold : ∀ {ℓ} (A : DistOpAlg ℓ) → Carrier A → ℕ → Carrier A
fold A a0 zero    = a0
fold A a0 (suc n) = U A (fold A a0 n)

-- fold is a homomorphism NAlg → A
mkFold : ∀ {ℓ} (A : DistOpAlg ℓ) (a0 : Carrier A) → HomAlg NAlg A
mkFold A a0 .f   = fold A a0
mkFold A a0 .hom n = refl  -- by definition: fold (suc n) = U (fold n)

-- Uniqueness: any hom f with f 0 = a0 equals fold A a0
fold-uniq
  : ∀ {ℓ} (A : DistOpAlg ℓ) (a0 : Carrier A)
    (h : HomAlg NAlg A) → (f h zero ≡ a0)
    → ∀ n → f h n ≡ fold A a0 n
fold-uniq A a0 h f0 zero    = f0
fold-uniq A a0 h f0 (suc n) =
  trans (hom h n) (cong (U A) (fold-uniq A a0 h f0 n))
