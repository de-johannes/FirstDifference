{-# OPTIONS --safe #-}

-- | Step 05: Semilattice
-- |
-- | Purpose:
-- |   Provide (meet/join) semilattice structure on Dist-vectors derived from drift/join.
-- |
-- | Method:
-- |   Reuse of Step02/03 results:
-- |     • operations:    drift, join, all-false, all-true  (from Step02)
-- |     • vector laws:   drift-assoc/comm, join-assoc/comm, drift-zeroʳ (from Step02 soundness)
-- |     • soundness:     idempotence/units/zeros via sound-* wrappers (from Step03 soundness)
-- |
-- | Guarantee:
-- |   All fields are inhabited by previously verified proofs (no axioms).
-- |
-- | Notes:
-- |   Finite families only; prefer our Bool from Step01 to avoid ambiguity.

module Structures.S02_OrderCategories.Step05_Semilattice where

------------------------------------------------------------------------
-- Imports
------------------------------------------------------------------------

open import Agda.Primitive
  using (Level; _⊔_; lsuc; lzero)

-- Core ops on distinction vectors
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; all-false; all-true)

-- Vector-level algebraic laws (certificates) — includes right zero for drift
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  using ( drift-assoc
        ; drift-comm
        ; join-assoc
        ; join-comm
        ; drift-zeroʳ)

-- Soundness wrappers (idempotence, units, left zero), no re-exports of drift-zeroʳ here
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-idempotent
        ; sound-drift-zeroˡ
        ; sound-join-idempotent
        ; sound-join-oneˡ
        ; sound-join-oneʳ)


------------------------------------------------------------------------
-- Meet-semilattice (with bottom)
------------------------------------------------------------------------

record MeetSemilattice⊥ (n : ℕ) : Set where
  field
    _⋀_     : Dist n → Dist n → Dist n
    assoc   : ∀ (x y z : Dist n) → _⋀_ (_⋀_ x y) z ≡ _⋀_ x (_⋀_ y z)
    comm    : ∀ (x y   : Dist n) → _⋀_ x y ≡ _⋀_ y x
    idemp   : ∀ (x     : Dist n) → _⋀_ x x ≡ x
    bottom  : Dist n
    absorbˡ : ∀ (x     : Dist n) → _⋀_ bottom x ≡ bottom
    absorbʳ : ∀ (x     : Dist n) → _⋀_ x bottom ≡ bottom

-- Instance for distinction vectors: meet = drift, bottom = all-false
meetSemilatticeᵈ : ∀ {n} → MeetSemilattice⊥ n
meetSemilatticeᵈ {n} = record
  { _⋀_     = drift
  ; assoc   = drift-assoc
  ; comm    = drift-comm
  ; idemp   = sound-drift-idempotent
  ; bottom  = all-false n
  ; absorbˡ = λ x → sound-drift-zeroˡ x
  ; absorbʳ = λ x → drift-zeroʳ x
  }

------------------------------------------------------------------------
-- Join-semilattice (with top)
------------------------------------------------------------------------

record JoinSemilattice⊤ (n : ℕ) : Set where
  field
    _⋁_    : Dist n → Dist n → Dist n
    assoc  : ∀ (x y z : Dist n) → _⋁_ (_⋁_ x y) z ≡ _⋁_ x (_⋁_ y z)
    comm   : ∀ (x y   : Dist n) → _⋁_ x y ≡ _⋁_ y x
    idemp  : ∀ (x     : Dist n) → _⋁_ x x ≡ x
    top    : Dist n
    unitˡ  : ∀ (x     : Dist n) → _⋁_ top x ≡ top
    unitʳ  : ∀ (x     : Dist n) → _⋁_ x top ≡ top

-- Instance for distinction vectors: join = join, top = all-true
joinSemilatticeᵈ : ∀ {n} → JoinSemilattice⊤ n
joinSemilatticeᵈ {n} = record
  { _⋁_   = join
  ; assoc = join-assoc
  ; comm  = join-comm
  ; idemp = sound-join-idempotent
  ; top   = all-true n
  ; unitˡ = λ x → sound-join-oneˡ x
  ; unitʳ = λ x → sound-join-oneʳ x
  }
