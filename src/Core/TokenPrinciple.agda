{-# OPTIONS --safe #-}

-- | The Token Principle: The foundational axiom that any material token
-- | instantiates the First Difference D0. This is the basis for constructing
-- | Boolean logic from pure distinction processes.
module Core.TokenPrinciple where

open import Agda.Primitive using (Level; lsuc; _⊔_)

-- | Clean, axioms-free interface for the Token Principle
-- | This record encapsulates the core insight: material existence
-- | implies the capacity to make distinctions
record TokenPrinciple (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    D0       : Set ℓ₁          -- The First Difference as a type
    Token    : Set ℓ₂          -- The notion of a material token
    token    : Token           -- Evidence: at least one token exists
    token⇒D0 : Token → D0      -- Key principle: any token instantiates D0

-- Make the record fields directly accessible
open TokenPrinciple public
