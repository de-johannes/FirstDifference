module Core.Irrefutable where

open import Agda.Primitive using (Level)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Core.TokenPrinciple

-- Parametric, machine-checked irrefutability:
-- Given TP, "¬ D0" collapses to ⊥
module Irrefutable {ℓ₁ ℓ₂ : Level} (TP : TokenPrinciple ℓ₁ ℓ₂) where
  private
    D0′       = TokenPrinciple.D0 TP
    Token′    = TokenPrinciple.Token TP
    token′    = TokenPrinciple.token TP
    token⇒D0′ = TokenPrinciple.token⇒D0 TP

  -- The core irrefutability theorem: denying D0 requires instantiating it
  irrefutable : ¬ D0′ → ⊥
  irrefutable notD0 = notD0 (token⇒D0′ token′)
