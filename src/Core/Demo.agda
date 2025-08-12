module Core.Demo where

open import Data.Unit using (⊤; tt)
open import Core.TokenPrinciple
open import Core.Irrefutable

-- Simple demo instance of Token Principle
TP⊤ : TokenPrinciple lzero lzero
TP⊤ .TokenPrinciple.D0       = ⊤
TP⊤ .TokenPrinciple.Token    = ⊤  
TP⊤ .TokenPrinciple.token    = tt
TP⊤ .TokenPrinciple.token⇒D0 = λ _ → tt

-- Demo of irrefutability
module DemoIrrefutable = Irrefutable TP⊤
