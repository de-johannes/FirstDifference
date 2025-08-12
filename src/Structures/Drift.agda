module Structure.Drift where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
_≢_ {A} x y = x ≡ y → ⊥

data Diff : Set where
  D0   : Diff
  next : Diff → Diff

next-injective : {x y : Diff} → next x ≡ next y → x ≡ y
next-injective refl = refl

next-neq : (d : Diff) → next d ≢ d
next-neq D0 ()
next-neq (next d) eq = next-neq d (next-injective eq)

iter : Nat → Diff
iter zero    = D0
iter (suc n) = next (iter n)

second-difference : Σ Diff (λ d₁ → d₁ ≢ D0)
second-difference = next D0 , next-neq D0

drift-necessary : (n : Nat) → Σ Diff (λ d' → d' ≢ iter n)
drift-necessary n = next (iter n) , next-neq (iter n)
