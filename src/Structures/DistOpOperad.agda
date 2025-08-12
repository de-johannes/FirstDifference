module Structures.DistOpOperad where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Unary operad: one generator; algebras = (A , U : A → A)
------------------------------------------------------------------------

record Operad₁ (ℓ : Level) : Set (lsuc ℓ) where
  field
    Op       : Set ℓ          -- operations; we take Op ≃ ⊤ (one op)
    unit     : Op             -- η
    comp     : Op → Op → Op   -- γ : O×O → O   (unary specialization)
    unitL    : ∀ o → comp o unit ≡ o
    unitR    : ∀ o → comp unit o ≡ o
    assoc    : ∀ o₁ o₂ o₃ → comp (comp o₁ o₂) o₃ ≡ comp o₁ (comp o₂ o₃)

-- Concrete unary operad with a single operation • and composition ≡ monoid on ⊤.
UnaryOp : Operad₁ lzero
UnaryOp .Operad₁.Op     = ⊤
UnaryOp .Operad₁.unit   = tt
UnaryOp .Operad₁.comp _ _ = tt
UnaryOp .Operad₁.unitL _ = refl
UnaryOp .Operad₁.unitR _ = refl
UnaryOp .Operad₁.assoc _ _ _ = refl

-- Algebras for this operad: endomorphism pairs (A , U)
record DistOpAlg (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    U       : Carrier → Carrier
open DistOpAlg public

-- Morphisms: f ∘ U = U ∘ f
record HomAlg {ℓ} (A B : DistOpAlg ℓ) : Set (lsuc ℓ) where
  field
    f   : Carrier A → Carrier B
    hom : ∀ x → f (U A x) ≡ U B (f x)
open HomAlg public

-- Category structure on algebras (needed for the functor later).
idAlg : ∀ {ℓ} (A : DistOpAlg ℓ) → HomAlg A A
idAlg A .f   = λ x → x
idAlg A .hom = λ _ → refl

_∘Alg_ : ∀ {ℓ} {A B C : DistOpAlg ℓ} → HomAlg B C → HomAlg A B → HomAlg A C
(g ∘Alg h) .f   = λ x → f g (f h x)
(g ∘Alg h) .hom x =
  begin
    f g (U _ (f h x))       ≡⟨ cong (f g) (hom h x) ⟩
    f g (U _ (f h x))       ≡⟨ hom g (f h x) ⟩
    U _ (f g (f h x))       ∎
  where
    open Relation.Binary.PropositionalEquality
    begin_ = λ z → z
    _≡⟨_⟩_ = λ a _ b → trans a b
    _∎      = λ z → z

-- Initial algebra (ℕ , suc)
NAlg : DistOpAlg lzero
NAlg .Carrier = ℕ
NAlg .U       = suc

-- Primitive recursion/fold into any algebra
fold : ∀ {ℓ} (A : DistOpAlg ℓ) → Carrier A → ℕ → Carrier A
fold A a₀ zero    = a₀
fold A a₀ (suc n) = U A (fold A a₀ n)

-- Universal morphism from (ℕ,succ) to A given a₀ : A
mkFold : ∀ {ℓ} (A : DistOpAlg ℓ) (a₀ : Carrier A) → HomAlg NAlg A
mkFold A a₀ .f     = fold A a₀
mkFold A a₀ .hom n = refl

-- Uniqueness of folds (initiality)
fold-uniq :
  ∀ {ℓ} (A : DistOpAlg ℓ) (a₀ : Carrier A)
    (h : HomAlg NAlg A)
    (f₀ : f h zero ≡ a₀)
  → ∀ n → f h n ≡ fold A a₀ n
fold-uniq A a₀ h f₀ zero    = f₀
fold-uniq A a₀ h f₀ (suc n) =
  trans (hom h n) (cong (U A) (fold-uniq A a₀ h f₀ n))
