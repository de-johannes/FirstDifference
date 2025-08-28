{-# OPTIONS --safe #-}

module Examples.EFI_FoldMap_SmokeTest where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Nat-Operatoren nur QUALIFIZIERT nutzen, um Kollisionen zu vermeiden
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)

open import Structures.Step7_DriftGraph using (DriftGraph ; Node)
open import Structures.Step10_FoldMap   using (FoldMap)

-- Wir aliasen das Core-Modul, damit wir seine Projektionen leicht referenzieren
import Physics.Step14_EFI_Core as EFIcore
open EFIcore using (Semiring ; EFI)

-- Ein einfacher ℕ-Semiring
natSemiring : Semiring lzero
natSemiring = record
  { Carrier = ℕ
  ; zero    = 0
  ; one     = 1
  ; _+_     = Nat._+_
  ; _*_     = Nat._*_
  }

-- EFI-Instanz auf FoldMap mit Dummy-Gewichten/Observable = 1
EFI-on-FoldMap
  : ∀ {G : DriftGraph} {rank : _}
  → (fm : FoldMap G rank)
  → (μ  : List Node)
  → EFI lzero lzero lzero lzero lzero lzero
EFI-on-FoldMap {G} {rank} fm μ = record
  { Θ        = Node
  ; SR       = natSemiring
  ; WR       = natSemiring
  ; WQTop    = ℕ
  ; WQFld    = ℕ
  ; WQSem    = ℕ
  ; Q        = λ _ → 1
  ; Sfield   = λ _ → 1
  ; Xi       = λ _ → 1
  ; O        = λ _ → 1
  ; μ        = μ
  ; Comb     = record { combine = λ q s xi → Nat._*_ (Nat._*_ q s) xi }
  ; scale    = λ w v → Nat._*_ w v
  }

-- Kernaussage: Für EINE FIXE Instanz efi stimmt ihre lokale Faltung mit length überein.
fold≡length
  : ∀ {G : DriftGraph} {rank : _}
  → (fm  : FoldMap G rank)
  → (μ₀  : List Node)                                    -- efi bleibt fix!
  → (μ   : List Node)                                    -- über diese Liste falten wir
  → EFIcore.EFI.fold (EFI-on-FoldMap fm μ₀) μ ≡ length μ
fold≡length fm μ₀ []       = refl
fold≡length fm μ₀ (_ ∷ μ′) = cong suc (fold≡length fm μ₀ μ′)

-- Hauptlemma: Erwartungswert = Länge des gespeicherten Maßes μ
expect≡length
  : ∀ {G : DriftGraph} {rank : _}
  → (fm : FoldMap G rank)
  → (μ  : List Node)
  → EFIcore.EFI.expect (EFI-on-FoldMap fm μ) ≡ length μ
expect≡length fm μ = fold≡length fm μ μ
