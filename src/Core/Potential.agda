{-# OPTIONS --safe #-}
module Core.Potential where

open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Core.TokenPrinciple

-- Universen (generisch halten)
postulate
  ℓP ℓD : Level

-- Opaquer Träger: keine Konstruktoren, keine Eliminatoren vorgegeben.
postulate
  Pot   : Set ℓP

-- Bipolare Zielstruktur (minimales Unterscheidungspaar mit Involution)
record Bipolar (ℓ : Level) : Set (lsuc ℓ) where
  field
    B           : Set ℓ
    inv         : B → B
    involutive  : ∀ b → inv (inv b) ≡ b
    _≢_         : B → B → Set      -- Ungleichheit als Prädikat
    nontrivial  : ∀ b → inv b ≢ b

-- Act-Schema: lizenziert (führt aber nicht aus!) α : Pot → B
record ActSchema : Set (lsuc (ℓP ⊔ ℓD)) where
  field
    bp : Bipolar ℓD
    α  : Pot → Bipolar.B bp

-- Brücke: Aus (ActSchema, p : Pot) wird eine TokenPrinciple-Instanz
TP-from-Potential : ActSchema → Pot → TokenPrinciple ℓD ℓP
TP-from-Potential AS p =
  record
    { D0       = Bipolar.B (ActSchema.bp AS)
    ; Token    = Pot
    ; token    = p
    ; token⇒D0 = ActSchema.α AS
    }