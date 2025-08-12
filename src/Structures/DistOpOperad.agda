module Structures.DistOpOperad where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- A simple unary operad wrapper (placeholder for later extensions)
------------------------------------------------------------------------

record Operad₁ (ℓ : Level) : Set (lsuc ℓ) where
  field
    Op    : Set ℓ
    unit  : Op
    comp  : Op → Op → Op
    unitL : ∀ o → comp o unit ≡ o
    unitR : ∀ o → comp unit o ≡ o
    assoc : ∀ o₁ o₂ o₃ → comp (comp o₁ o₂) o₃ ≡ comp o₁ (comp o₂ o₃)

UnaryOp : Operad₁ lzero
UnaryOp .Operad₁.Op          = ⊤
UnaryOp .Operad₁.unit        = tt
UnaryOp .Operad₁.comp _ _    = tt
UnaryOp .Operad₁.unitL _     = refl
UnaryOp .Operad₁.unitR _     = refl
UnaryOp .Operad₁.assoc _ _ _ = refl

------------------------------------------------------------------------
-- DistOp algebras: (A , U : A → A)
------------------------------------------------------------------------

record DistOpAlg (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    U       : Carrier → Carrier
open DistOpAlg public

-- Morphisms between possibly different universe levels
record HomAlg {ℓ₁ ℓ₂ : Level}
              (A : DistOpAlg ℓ₁) (B : DistOpAlg ℓ₂)
              : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    f   : Carrier A → Carrier B
    hom : ∀ x → f (U A x) ≡ U B (f x)
open HomAlg public

-- Identity morphism
idAlg : ∀ {ℓ} (A : DistOpAlg ℓ) → HomAlg A A
idAlg A .f   = λ x → x
idAlg A .hom = λ _ → refl

-- Composition of morphisms
_∘Alg_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : DistOpAlg ℓ₁} {B : DistOpAlg ℓ₂} {C : DistOpAlg ℓ₃} →
  HomAlg B C → HomAlg A B → HomAlg A C
(g ∘Alg h) .f     = λ x → f g (f h x)
(g ∘Alg h) .hom x =
  trans (cong (f g) (hom h x)) (hom g (f h x))

------------------------------------------------------------------------
-- Initial algebra (ℕ, suc) and fold
------------------------------------------------------------------------

NAlg : DistOpAlg lzero
NAlg .Carrier = ℕ
NAlg .U       = suc

fold : ∀ {ℓ} (A : DistOpAlg ℓ) → Carrier A → ℕ → Carrier A
fold A a₀ zero    = a₀
fold A a₀ (suc n) = U A (fold A a₀ n)

-- Universal morphism from NAlg to A (any universe level)
mkFold : ∀ {ℓ} (A : DistOpAlg ℓ) (a₀ : Carrier A) → HomAlg NAlg A
mkFold A a₀ .f     = fold A a₀
mkFold A a₀ .hom _ = refl

-- Uniqueness of folds (initiality proof)
fold-uniq :
  ∀ {ℓ} (A : DistOpAlg ℓ) (a₀ : Carrier A)
    (h : HomAlg NAlg A) (f₀ : f h zero ≡ a₀)
  → ∀ n → f h n ≡ fold A a₀ n
fold-uniq A a₀ h f₀ zero    = f₀
fold-uniq A a₀ h f₀ (suc n) =
  trans (hom h n) (cong (U A) (fold-uniq A a₀ h f₀ n))

------------------------------------------------------------------------
-- (Demo) helpers
------------------------------------------------------------------------

plus : ℕ → ℕ → ℕ
plus k n = n + k

plus-hom : ∀ k n → plus k (suc n) ≡ suc (plus k n)
plus-hom _ _ = refl

shiftHom : ℕ → HomAlg NAlg NAlg
shiftHom k .f     = plus k
shiftHom k .hom n = plus-hom k n

-- Identity shift: +0 is the identity morphism on NAlg
shift-id : ∀ n → plus 0 n ≡ n
shift-id _ = refl
