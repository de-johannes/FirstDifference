-- File: src/Examples/EFI_FoldMap_SmokeTest.agda
{-# OPTIONS --safe #-}

module Examples.EFI_FoldMap_SmokeTest where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- WICHTIG: Nat-Operatoren NICHT unqualifiziert importieren
open import Data.Nat as Nat using (ℕ; zero; suc)  -- kein _+_, _*_
open import Data.List using (List; []; _∷_; length)

open import Structures.Step7_DriftGraph using (DriftGraph ; Node)
open import Structures.Step10_FoldMap   using (FoldMap)
open import Physics.Step14_EFI_Core     renaming (Semiring to Semiring′ ; EFI to EFI′)

-- Einfacher ℕ-Semiring mit QUALIFIZIERTEN Ops
natSemiring : Semiring′ lzero
natSemiring = record
  { Carrier = ℕ
  ; zero    = 0
  ; one     = 1
  ; _+_     = Nat._+_
  ; _*_     = Nat._*_       -- aus Data.Nat qualifiziert
  }

-- EFI auf FoldMap mit Dummy-Gewichten/Observable = 1
EFI-on-FoldMap
  : ∀ {G : DriftGraph} {rank : _}
  → (fm : FoldMap G rank)
  → (μ  : List Node)
  → EFI′ lzero lzero lzero lzero lzero lzero
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

-- Beweis: expect ≡ length μ (bei Q=S=Ξ=1 und O=1)
expect≡length
  : ∀ {G : DriftGraph} {rank : _}
  → (fm : FoldMap G rank)
  → (μ  : List Node)
  → let efi = EFI-on-FoldMap fm μ in Physics.Step14_EFI_Core.EFI.expect efi ≡ length μ
expect≡length fm []       = refl
expect≡length fm (_ ∷ μ′) = cong suc (expect≡length fm μ′)
