{-# OPTIONS --safe #-}

-- Minimal, emergent equality
module Helpers.Equality where

open import Agda.Primitive using (Level; _⊔_; lsuc)

infix 4 _≈_

-- Parametric equality living in the same universe as A.
-- Written as an indexed family to stay minimal.
data _≈_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl≈ : x ≈ x

-- Symmetry
sym≈ : ∀ {ℓ A} {x y : A} → x ≈ y → y ≈ x
sym≈ refl≈ = refl≈

-- Transitivity
trans≈ : ∀ {ℓ A} {x y z : A} → x ≈ y → y ≈ z → x ≈ z
trans≈ refl≈ refl≈ = refl≈

-- Congruence for unary functions
cong≈ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
       (f : A → B) {x y : A} → x ≈ y → f x ≈ f y
cong≈ f refl≈ = refl≈

-- Congruence for binary functions
cong₂≈ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
        (g : A → B → C) {x x' : A} {y y' : B}
        → x ≈ x' → y ≈ y' → g x y ≈ g x' y'
cong₂≈ g refl≈ refl≈ = refl≈

-- (Optional) Equivalence record to re-export when needed.
record IsEquivalence {ℓ} {A : Set ℓ} (_≈_ : A → A → Set ℓ) : Set (ℓ ⊔ lsuc ℓ) where
  field
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

-- Our equality is an equivalence (proof packaged)
≈-isEquivalence : ∀ {ℓ A} → IsEquivalence (λ (x y : A) → x ≈ y)
≈-isEquivalence = record
  { refl  = refl≈
  ; sym   = sym≈
  ; trans = trans≈
  }
