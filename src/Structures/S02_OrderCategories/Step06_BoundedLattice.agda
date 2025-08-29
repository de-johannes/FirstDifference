-- src/Structures/S02_OrderCategories/Step06_BoundedLattice.agda
{-# OPTIONS --safe #-}

-- | Step 06: Bounded lattice on distinction vectors
-- |
-- | Purpose:
-- |   Bundle both semilattices (meet/join) together with absorption
-- |   and top/bottom units into a single bounded lattice interface.
-- |
-- | Method:
-- |   Reuse machine-checked vector laws from Step02/Step03. No new axioms.

module Structures.S02_OrderCategories.Step06_BoundedLattice where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Core types/ops
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; neg; all-false; all-true)

-- Vector-level laws (assoc/comm/units…)
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  using (drift-assoc; drift-comm; drift-identityʳ; drift-zeroʳ
       ; join-assoc;  join-comm)
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-idempotent
        ; sound-drift-identityˡ; sound-drift-zeroˡ; sound-drift-absorb
        ; sound-join-idempotent
        ; sound-join-identityˡ; sound-join-identityʳ
        ; sound-join-oneˡ;      sound-join-oneʳ
        ; sound-join-absorb
        )

------------------------------------------------------------------------
-- Bounded lattice (meet/join with top/bottom and absorption)
------------------------------------------------------------------------

record BoundedLattice (n : ℕ) : Set where
  field
    -- operations
    _⋀_  : Dist n → Dist n → Dist n
    _⋁_  : Dist n → Dist n → Dist n
    ⊥     : Dist n
    ⊤     : Dist n

    -- meet laws
    ⋀-assoc   : ∀ x y z → _⋀_ (_⋀_ x y) z ≡ _⋀_ x (_⋀_ y z)
    ⋀-comm    : ∀ x y   → _⋀_ x y ≡ _⋀_ y x
    ⋀-idemp   : ∀ x     → _⋀_ x x ≡ x
    ⋀-unitˡ   : ∀ x     → _⋀_ ⊤ x ≡ x
    ⋀-unitʳ   : ∀ x     → _⋀_ x ⊤ ≡ x
    ⋀-absorbˡ : ∀ x     → _⋀_ ⊥ x ≡ ⊥
    ⋀-absorbʳ : ∀ x     → _⋀_ x ⊥ ≡ ⊥

    -- join laws
    ⋁-assoc   : ∀ x y z → _⋁_ (_⋁_ x y) z ≡ _⋁_ x (_⋁_ y z)
    ⋁-comm    : ∀ x y   → _⋁_ x y ≡ _⋁_ y x
    ⋁-idemp   : ∀ x     → _⋁_ x x ≡ x
    ⋁-unitˡ   : ∀ x     → _⋁_ ⊥ x ≡ x
    ⋁-unitʳ   : ∀ x     → _⋁_ x ⊥ ≡ x
    ⋁-absorbˡ : ∀ x     → _⋁_ ⊤ x ≡ ⊤
    ⋁-absorbʳ : ∀ x     → _⋁_ x ⊤ ≡ ⊤

    -- absorption laws (lattice coherence)
    absorb⋀   : ∀ x y → _⋀_ x (_⋁_ x y) ≡ x
    absorb⋁   : ∀ x y → _⋁_ x (_⋀_ x y) ≡ x

-- Concrete instance for Dist n (meet = drift, join = join)
boundedLatticeᵈ : ∀ {n} → BoundedLattice n
boundedLatticeᵈ {n} = record
  { _⋀_   = drift
  ; _⋁_   = join
  ; ⊥     = all-false n
  ; ⊤     = all-true n
  ; ⋀-assoc   = drift-assoc
  ; ⋀-comm    = drift-comm
  ; ⋀-idemp   = sound-drift-idempotent
  ; ⋀-unitˡ   = λ x → sound-drift-identityˡ x
  ; ⋀-unitʳ   = λ x → drift-identityʳ x
  ; ⋀-absorbˡ = λ x → sound-drift-zeroˡ x
  ; ⋀-absorbʳ = λ x → drift-zeroʳ x
  ; ⋁-assoc   = join-assoc
  ; ⋁-comm    = join-comm
  ; ⋁-idemp   = sound-join-idempotent
  ; ⋁-unitˡ   = λ x → sound-join-identityˡ x
  ; ⋁-unitʳ   = λ x → sound-join-identityʳ x
  ; ⋁-absorbˡ = λ x → sound-join-oneˡ x
  ; ⋁-absorbʳ = λ x → sound-join-oneʳ x
  ; absorb⋀   = λ x y → sound-drift-absorb x y
  ; absorb⋁   = λ x y → sound-join-absorb x y
  }