{-# OPTIONS --safe #-}

module Structures.Step14_EFI where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- 0) Minimale Algebra-Interfaces (ohne Gesetzesbeweise)
------------------------------------------------------------------------

record Semiring (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    zero    : Carrier
    one     : Carrier
    _+_     : Carrier → Carrier → Carrier
    _*_     : Carrier → Carrier → Carrier

open Semiring public

-- Für das Kombinieren der drei Gewichtskomponenten in das Arbeits-Semiring
record WeightCombiner (ℓW ℓQT ℓQF ℓQS : Level)
                      (W  : Set ℓW)
                      (WQTop : Set ℓQT)
                      (WQFld : Set ℓQF)
                      (WQSem : Set ℓQS)
                      : Set (lsuc (ℓW ⊔ ℓQT ⊔ ℓQF ⊔ ℓQS)) where
  field
    combine : WQTop → WQFld → WQSem → W        -- (Q,S,Ξ) ↦ W

open WeightCombiner public

------------------------------------------------------------------------
-- 1) EFI-Träger: Konfigurationen Θ, Observables, Gewichte
------------------------------------------------------------------------

record EFI (ℓΘ ℓV ℓW ℓQT ℓQF ℓQS : Level) : Set (lsuc (ℓΘ ⊔ ℓV ⊔ ℓW ⊔ ℓQT ⊔ ℓQF ⊔ ℓQS)) where
  field
    Θ        : Set ℓΘ                     -- Konfigurationsraum
    SR       : Semiring ℓV                -- Werte-/Ergebnis-Semiring (für Observables & Expectation)
    WR       : Semiring ℓW                -- Arbeits-/Gewichts-Semiring (zum Skalieren)
    Comb     : WeightCombiner (ℓW) (ℓQT) (ℓQF) (ℓQS)
                               (Semiring.Carrier WR)
                               (Set ℓQT) (Set ℓQF) (Set ℓQS)
      -- ^ Achtung: wir instanziieren die Typargumente unten in den Feldern explizit.

    -- Gewichtskomponenten (diskret; kontinuierliche Fälle können später aufbauen)
    WQTop    : Set ℓQT                    -- Typ für Q[θ]
    WQFld    : Set ℓQF                    -- Typ für S_field[θ]
    WQSem    : Set ℓQS                    -- Typ für Ξ_sem[θ]

    Q        : Θ → WQTop                  -- topologische Phase/Anteil    (diskret/abstrakt)
    Sfield   : Θ → WQFld                  -- Felddynamik-Anteil           (abstrakt)
    Xi       : Θ → WQSem                  -- semantisches Gewicht         (real/positiv im Paper; hier abstrakt)

    -- Beobachtbare
    Observable : Set ℓV                   -- meist = Carrier SR
    O          : Θ → Observable

    -- Diskretes "Maß": endliche Konfigurationsliste für die Summe
    μ        : List Θ

  open Semiring SR using (Carrier ; zero ; one ; _+_ ; _*_) renaming (Carrier to V)
  open Semiring WR using (Carrier ; zero ; one ; _+_ ; _*_) renaming (Carrier to W)
  open WeightCombiner Comb using (combine)

  -- Skalarwirkung W × V → V (wie "Scale" für Erwartungswert)
  -- In einfachen Setups nehmen wir dieselbe Multiplikation wie in SR,
  -- wenn V ≡ W gilt. Für allgemeine Fälle kann man hier eine Aktion injizieren.
  field
    scale : W → V → V

  ----------------------------------------------------------------------
  -- 2) Gesamtgewicht w[θ] = combine (Q θ) (Sfield θ) (Xi θ)
  ----------------------------------------------------------------------
  totalWeight : Θ → W
  totalWeight θ = combine (Q θ) (Sfield θ) (Xi θ)

  ----------------------------------------------------------------------
  -- 3) Erwartungswert: endliche Summe   E[O] = Σ_{θ∈μ}  w[θ] ⋅ O[θ]
  ----------------------------------------------------------------------
  expect : V
  expect = fold μ
    where
      fold : List Θ → V
      fold []       = zero
      fold (θ ∷ ts) = _+_ (scale (totalWeight θ) (O θ)) (fold ts)

------------------------------------------------------------------------
-- 2) Beispiel-/Dummy-Instanzen (nur wenn du was Konkretes willst)
------------------------------------------------------------------------
-- Hinweis: In deinem Repo nutzt du vermutlich eigene Zahl-/Feldtypen.
-- Diese Sektion ist optional. Du kannst sie entfernen, wenn du eigene
-- Semirings einbindest (z. B. auf ℕ, ℤ, ℚ, oder Reals).

-- Minimaler Semiring über Bool (als Demonstrator; NICHT physikalisch sinnvoll)
-- Addition = OR, Multiplikation = AND
record BoolSR : Set where
  constructor mk
  field
    SRb : Semiring lzero

open BoolSR

boolSR : BoolSR
boolSR = mk (record
  { Carrier = Bool
  ; zero    = false
  ; one     = true
  ; _+_     = λ a b → if a then true else b
  ; _*_     = λ a b → if a then b else false
  })

-- Beispiel-Combiner, der drei Bools "multipliziert" (AND):
BoolComb : WeightCombiner lzero lzero lzero lzero Bool Bool Bool Bool
BoolComb = record { combine = λ q s x → (if q then (if s then x else false) else false) }

-- Beispiel-EFI über Bool (nur als Kompilat-Dummy)
module Demo where
  open import Data.Bool using (Bool; true; false)
  open Semiring (SR boolSR .SRb) using (_+_; _*_; zero; one) renaming (Carrier to V)
  open Semiring (WR boolSR .SRb) using (_+_; _*_; zero; one) renaming (Carrier to W)
  open WeightCombiner BoolComb using (combine)

  -- Träger
  Θᵈ : Set
  Θᵈ = Bool

  -- Observable: identisch (nur Demo)
  Oᵈ : Θᵈ → V
  Oᵈ θ = θ

  -- Gewichte: trivial
  Qᵈ     : Θᵈ → Bool
  Qᵈ θ = θ
  Sᵈ     : Θᵈ → Bool
  Sᵈ θ = true
  Xiᵈ    : Θᵈ → Bool
  Xiᵈ θ = true

  μᵈ : List Θᵈ
  μᵈ = true ∷ false ∷ []

  EFIᵈ : EFI lzero lzero lzero lzero lzero lzero
  EFIᵈ = record
    { Θ        = Θᵈ
    ; SR       = (SR boolSR .SRb)
    ; WR       = (WR boolSR .SRb)
    ; Comb     = BoolComb
    ; WQTop    = Bool
    ; WQFld    = Bool
    ; WQSem    = Bool
    ; Q        = Qᵈ
    ; Sfield   = Sᵈ
    ; Xi       = Xiᵈ
    ; Observable = V
    ; O        = Oᵈ
    ; μ        = μᵈ
    ; scale    = _*_           -- hier: W ≡ V ≡ Bool, also AND
    }

  -- Erwartungswert im Demo: expect = true (weil nur θ=true trägt)
  _ : EFI.expect EFIᵈ ≡ true
  _ = refl
