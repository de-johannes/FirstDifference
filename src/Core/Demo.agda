module Core.Demo where

open import Agda.Primitive using (lzero)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

open import Core.TokenPrinciple
open import Core.Irrefutable

-- Trivial concrete instance: tokens and D0 are both inhabited by ⊤.
TP⊤ : TokenPrinciple lzero lzero
TP⊤ .TokenPrinciple.D0       = ⊤
TP⊤ .TokenPrinciple.Token    = ⊤
TP⊤ .TokenPrinciple.token    = tt
TP⊤ .TokenPrinciple.token⇒D0 = λ _ → tt

-- If someone assumes "¬ D0" here, we derive ⊥ (machine-checked, --safe).
open Irrefutable TP⊤
explode : ¬ (TokenPrinciple.D0 TP⊤) → ⊥
explode = irrefutable
