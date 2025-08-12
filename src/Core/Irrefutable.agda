{-# OPTIONS --safe #-}

-- | Machine-checked proof that the Token Principle is irrefutable
-- | This demonstrates that denying D0 leads to logical contradiction
module Core.Irrefutable where

open import Agda.Primitive using (Level)
open import Relation.Nullary using (¬_)  -- Negation
open import Data.Empty using (⊥)          -- Bottom type (contradiction)
open import Core.TokenPrinciple

-- | Parametric, machine-checked irrefutability theorem
-- | Given any instance of TokenPrinciple, denying D0 collapses to ⊥
module Irrefutable {ℓ₁ ℓ₂ : Level} (TP : TokenPrinciple ℓ₁ ℓ₂) where
  private
    -- Extract the components from our TokenPrinciple instance
    D0′       = TokenPrinciple.D0 TP
    Token′    = TokenPrinciple.Token TP
    token′    = TokenPrinciple.token TP
    token⇒D0′ = TokenPrinciple.token⇒D0 TP

  -- | The core irrefutability theorem: 
  -- | To deny D0, one must instantiate it (contradiction!)
  irrefutable : ¬ D0′ → ⊥
  irrefutable notD0 = notD0 (token⇒D0′ token′)
  -- Proof: We have a token, which instantiates D0,
  -- but we assumed ¬D0, so we get contradiction ⊥
