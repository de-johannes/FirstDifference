module Structures.DistOpOperad where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Simple unary operad structure (foundation for distinction operations)
------------------------------------------------------------------------

record Operad₁ (ℓ : Level) : Set (lsuc ℓ) where
  field
    Op    : Set ℓ
    unit  : Op
    comp  : Op → Op → Op
    unitL : ∀ o → comp o unit ≡ o
    unitR : ∀ o → comp unit o ≡ o
    assoc : ∀ o₁ o₂ o₃ → comp (comp o₁ o₂) o₃ ≡ comp o₁ (comp o₂ o₃)

-- Trivial unary operad: models pure iteration/succession
UnaryOp : Operad₁ lzero
UnaryOp .Operad₁.Op          = ⊤
UnaryOp .Operad₁.unit        = tt
UnaryOp .Operad₁.comp _ _    = tt
UnaryOp .Operad₁.unitL _     = refl
UnaryOp .Operad₁.unitR _     = refl
UnaryOp .Operad₁.assoc _ _ _ = refl

------------------------------------------------------------------------
-- DistOp algebras: (Carrier, Endomorphism)
-- Models systems with a single "successor/iteration" operation
------------------------------------------------------------------------

record DistOpAlg (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ      -- The carrier set
    U       : Carrier → Carrier  -- The unary operation ("next step")

open DistOpAlg public

-- Homomorphisms between algebras at possibly different universe levels
record HomAlg {ℓ₁ ℓ₂ : Level}
              (A : DistOpAlg ℓ₁) (B : DistOpAlg ℓ₂)
              : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    f   : Carrier A → Carrier B
    hom : ∀ x → f (U A x) ≡ U B (f x)  -- Structure preservation

open HomAlg public

-- Identity morphism
idAlg : ∀ {ℓ} (A : DistOpAlg ℓ) → HomAlg A A
idAlg A .f   = λ x → x
idAlg A .hom = λ _ → refl

-- Composition of algebra homomorphisms
_∘Alg_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
           {A : DistOpAlg ℓ₁} {B : DistOpAlg ℓ₂} {C : DistOpAlg ℓ₃} →
         HomAlg B C → HomAlg A B → HomAlg A C
(g ∘Alg h) .f     = λ x → f g (f h x)
(g ∘Alg h) .hom x = trans (cong (f g) (hom h x)) (hom g (f h x))

------------------------------------------------------------------------
-- Initial algebra: (ℕ, suc) - the canonical counting structure
-- This connects to semantic time from drift histories
------------------------------------------------------------------------

NAlg : DistOpAlg lzero
NAlg .Carrier = ℕ
NAlg .U       = suc  -- Successor operation = "one more semantic time unit"

-- Primitive recursion: the fold operation
fold : ∀ {ℓ} (A : DistOpAlg ℓ) → Carrier A → ℕ → Carrier A
fold A a₀ zero    = a₀
fold A a₀ (suc n) = U A (fold A a₀ n)

-- Universal morphism from NAlg to any algebra
mkFold : ∀ {ℓ} (A : DistOpAlg ℓ) (a₀ : Carrier A) → HomAlg NAlg A
mkFold A a₀ .f     = fold A a₀
mkFold A a₀ .hom _ = refl

-- Initiality proof: uniqueness of folds
fold-uniq : ∀ {ℓ} (A : DistOpAlg ℓ) (a₀ : Carrier A)
              (h : HomAlg NAlg A) (f₀ : f h zero ≡ a₀)
            → ∀ n → f h n ≡ fold A a₀ n
fold-uniq A a₀ h f₀ zero    = f₀
fold-uniq A a₀ h f₀ (suc n) =
  trans (hom h n) (cong (U A) (fold-uniq A a₀ h f₀ n))

------------------------------------------------------------------------
-- Semantic connection helpers
------------------------------------------------------------------------

-- Addition as endomorphism shift
plus : ℕ → ℕ → ℕ
plus k n = n + k

plus-hom : ∀ k n → plus k (suc n) ≡ suc (plus k n)
plus-hom _ _ = refl

-- Shift homomorphism: adds constant offset (models temporal advancement)
shiftHom : ℕ → HomAlg NAlg NAlg
shiftHom k .f     = plus k
shiftHom k .hom n = plus-hom k n

-- Identity shift: adding zero is identity
shift-id : ∀ n → plus 0 n ≡ n
shift-id n = +-identityʳ n
