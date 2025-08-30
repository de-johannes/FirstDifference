{-# OPTIONS --safe #-}

module Examples.EFI_FoldMap_SmokeTest where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Nat-Operatoren nur QUALIFIZIERT nutzen (vermeidet Kollisionen)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)

open import Structures.S03_ProcessGraphs.Step10_DriftGraph using (DriftGraph ; Node)
open import Structures.S04_Projection.Step15_FoldMap   using (FoldMap)

-- Physik-Core qualifiziert einbinden (wir nutzen Semiring, EFI, fold, expect)
open import Physics.Step01_EFI_Core as P using (Semiring; EFI)
import Physics.Step01_EFI_Core as Core  -- für Core.fold / Core.expect

------------------------------------------------------------------------
-- Nat-Semiring als einfachste Trägerstruktur
------------------------------------------------------------------------

natSemiring : Semiring lzero
natSemiring = record
  { Carrier = ℕ
  ; zero    = 0
  ; one     = 1
  ; _+_     = Nat._+_
  ; _*_     = Nat._*_
  }

------------------------------------------------------------------------
-- EFI auf FoldMap mit Dummy-Gewichten/Observable = 1
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Lemma über die Faltung: Für eine FIXE EFI-Instanz gilt fold efi μ = length μ
------------------------------------------------------------------------

fold≡length
  : ∀ {G : DriftGraph} {rank : _}
  → (fm  : FoldMap G rank)
  → (μ₀  : List Node)                          -- EFI-Instanz bleibt FIX
  → (μ   : List Node)                          -- über diese Liste falten wir
  → Core.fold (EFI-on-FoldMap fm μ₀) μ ≡ length μ
fold≡length fm μ₀ []       = refl
fold≡length fm μ₀ (_ ∷ μ′) = cong suc (fold≡length fm μ₀ μ′)

------------------------------------------------------------------------
-- Hauptlemma: Erwartungswert = Länge des gespeicherten Maßes μ
------------------------------------------------------------------------

expect≡length
  : ∀ {G : DriftGraph} {rank : _}
  → (fm : FoldMap G rank)
  → (μ  : List Node)
  → Core.expect (EFI-on-FoldMap fm μ) ≡ length μ
expect≡length fm μ = fold≡length fm μ μ
