{-# OPTIONS --safe #-}

-- | Step 05: Semilattice — Soundness Layer
-- |
-- | Purpose:
-- |   Provide soundness certificates (sound-…) for the semilattice
-- |   instances on distinction vectors. No new proofs.

module Structures.S02_OrderCategories.Step05_Semilattice_Soundness where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Structures.S01_BooleanCore.Step02_VectorOperations using (Dist)
open import Structures.S02_OrderCategories.Step05_Semilattice

------------------------------------------------------------------------
-- Re-export the concrete instances
------------------------------------------------------------------------

sound-meetSemilattice⊥ : ∀ {n} → MeetSemilattice⊥ n
sound-meetSemilattice⊥ {n} = meetSemilatticeᵈ {n}

sound-joinSemilattice⊤ : ∀ {n} → JoinSemilattice⊤ n
sound-joinSemilattice⊤ {n} = joinSemilatticeᵈ {n}

------------------------------------------------------------------------
-- Meet-semilattice (aliases)
------------------------------------------------------------------------

sound-⋀ : ∀ {n} → Dist n → Dist n → Dist n
sound-⋀ {n} = MeetSemilattice⊥._⋀_ (sound-meetSemilattice⊥ {n})

sound-⋀-assoc : ∀ {n} (x y z : Dist n) →
  sound-⋀ (sound-⋀ x y) z ≡ sound-⋀ x (sound-⋀ y z)
sound-⋀-assoc {n} x y z =
  MeetSemilattice⊥.assoc (sound-meetSemilattice⊥ {n}) x y z

sound-⋀-comm : ∀ {n} (x y : Dist n) → sound-⋀ x y ≡ sound-⋀ y x
sound-⋀-comm {n} x y =
  MeetSemilattice⊥.comm (sound-meetSemilattice⊥ {n}) x y

sound-⋀-idemp : ∀ {n} (x : Dist n) → sound-⋀ x x ≡ x
sound-⋀-idemp {n} x =
  MeetSemilattice⊥.idemp (sound-meetSemilattice⊥ {n}) x

sound-⊥ᵐ : ∀ {n} → Dist n
sound-⊥ᵐ {n} = MeetSemilattice⊥.bottom (sound-meetSemilattice⊥ {n})

sound-⋀-absorbˡ : ∀ {n} (x : Dist n) → sound-⋀ sound-⊥ᵐ x ≡ sound-⊥ᵐ
sound-⋀-absorbˡ {n} x =
  MeetSemilattice⊥.absorbˡ (sound-meetSemilattice⊥ {n}) x

sound-⋀-absorbʳ : ∀ {n} (x : Dist n) → sound-⋀ x sound-⊥ᵐ ≡ sound-⊥ᵐ
sound-⋀-absorbʳ {n} x =
  MeetSemilattice⊥.absorbʳ (sound-meetSemilattice⊥ {n}) x

------------------------------------------------------------------------
-- Join-semilattice (aliases)
------------------------------------------------------------------------

sound-⋁ : ∀ {n} → Dist n → Dist n → Dist n
sound-⋁ {n} = JoinSemilattice⊤._⋁_ (sound-joinSemilattice⊤ {n})

sound-⋁-assoc : ∀ {n} (x y z : Dist n) →
  sound-⋁ (sound-⋁ x y) z ≡ sound-⋁ x (sound-⋁ y z)
sound-⋁-assoc {n} x y z =
  JoinSemilattice⊤.assoc (sound-joinSemilattice⊤ {n}) x y z

sound-⋁-comm : ∀ {n} (x y : Dist n) → sound-⋁ x y ≡ sound-⋁ y x
sound-⋁-comm {n} x y =
  JoinSemilattice⊤.comm (sound-joinSemilattice⊤ {n}) x y

sound-⋁-idemp : ∀ {n} (x : Dist n) → sound-⋁ x x ≡ x
sound-⋁-idemp {n} x =
  JoinSemilattice⊤.idemp (sound-joinSemilattice⊤ {n}) x

sound-⊤ʲ : ∀ {n} → Dist n
sound-⊤ʲ {n} = JoinSemilattice⊤.top (sound-joinSemilattice⊤ {n})

sound-⋁-unitˡ : ∀ {n} (x : Dist n) → sound-⋁ sound-⊤ʲ x ≡ sound-⊤ʲ
sound-⋁-unitˡ {n} x =
  JoinSemilattice⊤.unitˡ (sound-joinSemilattice⊤ {n}) x

sound-⋁-unitʳ : ∀ {n} (x : Dist n) → sound-⋁ x sound-⊤ʲ ≡ sound-⊤ʲ
sound-⋁-unitʳ {n} x =
  JoinSemilattice⊤.unitʳ (sound-joinSemilattice⊤ {n}) x