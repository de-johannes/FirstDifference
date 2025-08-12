{-# OPTIONS --safe #-}

-- | Demonstration module: shows TokenPrinciple in action
-- | This provides concrete examples of the abstract theory
module Core.Demo where

open import Data.Unit using (⊤; tt)
open import Core.TokenPrinciple
open import Core.Irrefutable

-- | Simple demonstration instance of Token Principle
-- | Uses the unit type ⊤ for both D0 and Token
-- | This is the minimal non-trivial example
TP⊤ : TokenPrinciple lzero lzero
TP⊤ .TokenPrinciple.D0       = ⊤       -- First Difference is unit type
TP⊤ .TokenPrinciple.Token    = ⊤       -- Tokens are also unit type
TP⊤ .TokenPrinciple.token    = tt      -- The single token exists
TP⊤ .TokenPrinciple.token⇒D0 = λ _ → tt -- Any token gives unit value

-- | Demonstration of irrefutability using our example
-- | This module contains the proof that TP⊤ cannot be refuted
module DemoIrrefutable = Irrefutable TP⊤

-- The key insight: even with this trivial example, we get
-- a machine-verified proof that the Token Principle cannot
-- be consistently denied!
