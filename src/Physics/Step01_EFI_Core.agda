{-# OPTIONS --safe #-}

module Physics.Step01_EFI_Core where

open import Agda.Primitive using (Level; _⊔_; lsuc)
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

    -- Observable und Trägermaß (diskret)
    O        : Θ → Semiring.Carrier SR
    μ        : List Θ

    -- Kombinator (nutzt die obigen Typen)
    Comb     : WeightCombiner ℓW ℓQT ℓQF ℓQS
                             (Semiring.Carrier WR) WQTop WQFld WQSem

    -- Skalarwirkung W × V → V (z. B. identisch, falls V ≡ W)
    scale    : Semiring.Carrier WR → Semiring.Carrier SR → Semiring.Carrier SR

------------------------------------------------------------------------
-- Exportierte Hilfsfunktionen (von außen nutzbar)
------------------------------------------------------------------------

-- Gesamtgewicht einer Konfiguration θ
totalWeight
  : ∀ {ℓΘ ℓV ℓW ℓQT ℓQF ℓQS}
  → (efi : EFI ℓΘ ℓV ℓW ℓQT ℓQF ℓQS)
  → (θ   : EFI.Θ efi)
  → Semiring.Carrier (EFI.WR efi)
totalWeight efi θ =
  let open WeightCombiner (EFI.Comb efi) renaming (combine to combineW)
  in combineW (EFI.Q efi θ) (EFI.Sfield efi θ) (EFI.Xi efi θ)

-- Faltung über eine Liste von Zuständen (mit fixer EFI-Instanz)
fold
  : ∀ {ℓΘ ℓV ℓW ℓQT ℓQF ℓQS}
  → (efi : EFI ℓΘ ℓV ℓW ℓQT ℓQF ℓQS)
  → List (EFI.Θ efi)
  → Semiring.Carrier (EFI.SR efi)
fold efi [] =
  Semiring.zero (EFI.SR efi)
fold efi (θ ∷ ts) =
  let _+V_ = Semiring._+_ (EFI.SR efi)
      sc   = EFI.scale efi
  in  _+V_ (sc (totalWeight efi θ) (EFI.O efi θ)) (fold efi ts)

-- Erwartungswert: Faltung über das im Record gespeicherte μ
expect
  : ∀ {ℓΘ ℓV ℓW ℓQT ℓQF ℓQS}
  → (efi : EFI ℓΘ ℓV ℓW ℓQT ℓQF ℓQS)
  → Semiring.Carrier (EFI.SR efi)
expect efi = fold efi (EFI.μ efi)
