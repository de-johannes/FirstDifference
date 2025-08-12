module Core.TokenPrinciple where

open import Agda.Primitive using (Level; lsuc; _⊔_)

-- Clean, axioms-free interface for the Token Principle
-- Any material token instantiates the First Difference D0
record TokenPrinciple (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    D0       : Set ℓ₁          -- the First Difference as a type
    Token    : Set ℓ₂          -- the notion of a token
    token    : Token           -- at least one token occurs
    token⇒D0 : Token → D0      -- any token instantiates D0

open TokenPrinciple public
