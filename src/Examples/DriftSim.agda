module Examples.DriftSim where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Sum  using (_⊎_; inj₁; inj₂)
open import Data.Nat  using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Toy example: a tiny "drift" over one-bit distinctions, just to exercise `_⊎_`.

data Dist : Set where
  bit : Bool → Dist

-- Drift = Boolean AND on the underlying bit
drift : Dist → Dist → Dist
drift (bit b₁) (bit b₂) = bit (b₁ ∧ b₂)

-- One simulation step that returns either a "new" or a "stagnant" state
-- (purely illustrative; replace with your real logic later).
data StepTag : Set where New Stagnant : StepTag

step : Dist → Dist → (StepTag ⊎ Dist)
step d₁ d₂ with drift d₁ d₂
... | bit true  = inj₁ New
... | bit false = inj₂ (bit false)

-- Tiny sanity checks so CI does something nontrivial
step-true-true : step (bit true) (bit true) ≡ inj₁ New
step-true-true = refl

step-true-false : step (bit true) (bit false) ≡ inj₂ (bit false)
step-true-false = refl
