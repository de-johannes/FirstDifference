{-# OPTIONS --safe #-}

module Physics.Step14_EFI_Core where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Semiring & WeightCombiner
------------------------------------------------------------------------

record Semiring (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    zero    : Carrier
    one     : Carrier
    _+_     : Carrier → Carrier → Carrier
    _*_     : Carrier → Carrier → Carrier
open Semiring public

record WeightCombiner (ℓW ℓQT ℓQF ℓQS : Level)
                      (W     : Set ℓW)
                      (WQTop : Set ℓQT)
                      (WQFld : Set ℓQF)
                      (WQSem : Set ℓQS)
                      : Set (lsuc (ℓW ⊔ ℓQT ⊔ ℓQF ⊔ ℓQS)) where
  field combine : WQTop → WQFld → WQSem → W
open WeightCombiner public

------------------------------------------------------------------------
-- EFI (diskret: endliche Liste μ)
------------------------------------------------------------------------

record EFI (ℓΘ ℓV ℓW ℓQT ℓQF ℓQS : Level)
  : Set (lsuc (ℓΘ ⊔ ℓV ⊔ ℓW ⊔ ℓQT ⊔ ℓQF ⊔ ℓQS)) where
  field
    Θ        : Set ℓΘ
    SR       : Semiring ℓV
    WR       : Semiring ℓW

    -- Gewichtskomponenten
    WQTop    : Set ℓQT
    WQFld    : Set ℓQF
    WQSem    : Set ℓQS
    Q        : Θ → WQTop
    Sfield   : Θ → WQFld
    Xi       : Θ → WQSem

    -- Trägermaß (diskret) und Observable direkt im Träger von SR
    O        : Θ → Semiring.Carrier SR
    μ        : List Θ

    -- Kombinator (nutzt die obigen Typen)
    Comb     : WeightCombiner ℓW ℓQT ℓQF ℓQS
                             (Semiring.Carrier WR) WQTop WQFld WQSem

  -- sauber öffnen und klar benennen (keine Überladung)
  open Semiring SR using () renaming (Carrier to V; zero to zeroV; _+_ to _+V_)
  open Semiring WR using () renaming (Carrier to W)
  open WeightCombiner Comb renaming (combine to combineW)

  -- Skalarwirkung W × V → V
  field
    scale : W → V → V

  -- Gesamtgewicht
  totalWeight : Θ → W
  totalWeight θ = combineW (Q θ) (Sfield θ) (Xi θ)

  -- Erwartungswert: Σ_{θ∈μ} w[θ] ⋅ O[θ]
  expect : V
  expect = fold μ
    where
      fold : List Θ → V
      fold []       = zeroV
      fold (θ ∷ ts) = _+V_ (scale (totalWeight θ) (O θ)) (fold ts)
