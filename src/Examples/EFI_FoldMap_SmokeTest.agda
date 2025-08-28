{-# OPTIONS --safe #-}

module Examples.EFI_FoldMap_SmokeTest where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; length)

open import Structures.Step7_DriftGraph using (DriftGraph ; Node)
open import Structures.Step10_FoldMap   using (FoldMap)
open import Physics.Step14_EFI_Core     renaming (Semiring to Semiring′ ; EFI to EFI′)

-- Ein sehr einfacher ℕ-Semiring (Addition/Multiplikation)
natSemiring : Semiring′ lzero
natSemiring = record
  { Carrier = ℕ
  ; zero    = 0
  ; one     = 1
  ; _+_     = _+_
  ; _*_     = _*_
  }

-- Aus einer FoldMap + Knotenliste μ bauen wir eine konkrete EFI-Instanz:
-- Θ = Node ; SR = WR = ℕ-Semiring ; Q=S=Ξ=1 ; Observable O=1
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
  ; Comb     = record { combine = λ q s xi → (q * s) * xi }
  ; scale    = λ w v → w * v
  }

-- Wichtiger Basis-Beweis: mit Q=S=Ξ=1 und O=1 ist der Erwartungswert
-- genau die Anzahl der Knoten im Maß μ.
expect≡length
  : ∀ {G : DriftGraph} {rank : _}
  → (fm : FoldMap G rank)
  → (μ  : List Node)
  → let efi = EFI-on-FoldMap fm μ in Physics.Step14_EFI_Core.EFI.expect efi ≡ length μ
expect≡length fm []       = refl
expect≡length fm (_ ∷ μ′) =
  -- expect (θ ∷ μ′) = 1 * 1 + expect μ′  ≡ 1 + length μ′ ≡ length (θ ∷ μ′)
  -- Reduziert in ℕ by definitional equality → refl
  cong suc (expect≡length fm μ′)
