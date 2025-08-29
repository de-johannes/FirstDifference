{-# OPTIONS --safe #-}

-- Minimal function helpers
module Helpers.Function where

open import Agda.Primitive using (Level)

-- identity
id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

-- composition
infixr 9 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
      {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
      → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)
