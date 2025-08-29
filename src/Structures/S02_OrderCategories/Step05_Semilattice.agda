{-# OPTIONS --safe #-}

-- | Step 05: Semilattice
-- |
-- | Purpose:
-- |   Provide meet/join semilattice certificates on Dist-vectors, reusing
-- |   drift/join and their verified laws.
-- |
-- | Method:
-- |   Reuse of Step03 results:
-- |     • laws (Dist-level): sound-drift-assoc/comm, sound-join-assoc/comm
-- |     • idempotence:      sound-drift-idempotent, sound-join-idempotent
-- |
-- | Guarantee:
-- |   All fields are inhabited by existing proofs; no new axioms or re-proofs.
-- |
-- | Notes:
-- |   Bounds (⊥/⊤) handled elsewhere; Step05 focuses on semilattice laws only.

module Structures.S02_OrderCategories.Step05_Semilattice where

------------------------------------------------------------------------
-- Imports
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Core ops on distinction vectors
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join)

-- Dist-level law certificates + idempotence
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-assoc
        ; sound-drift-comm
        ; sound-join-assoc
        ; sound-join-comm
        ; sound-drift-idempotent
        ; sound-join-idempotent)

------------------------------------------------------------------------
-- Public API: operation aliases
------------------------------------------------------------------------

infixl 6 _∧_ _∨_

_∧_ : ∀ {n : ℕ} → Dist n → Dist n → Dist n
_∧_ = drift

_∨_ : ∀ {n : ℕ} → Dist n → Dist n → Dist n
_∨_ = join

------------------------------------------------------------------------
-- Semilattice records (minimal; no external theory)
------------------------------------------------------------------------

record IsSemilattice {ℓ : Level} {A : Set ℓ} (_∙_ : A → A → A) : Set ℓ where
  field
    assoc      : ∀ x y z → _∙_ x (_∙_ y z) ≡ _∙_ (_∙_ x y) z
    comm       : ∀ x y   → _∙_ x y ≡ _∙_ y x
    idempotent : ∀ x     → _∙_ x x ≡ x

------------------------------------------------------------------------
-- Drift-side semilattice (meet)
------------------------------------------------------------------------

isDriftSemilattice : ∀ {n : ℕ} → IsSemilattice (_∧_ {n})
isDriftSemilattice {n} = record
  { assoc      = sound-drift-assoc  {n}
  ; comm       = sound-drift-comm   {n}
  ; idempotent = sound-drift-idempotent {n}
  }

record DriftSemilattice (n : ℕ) : Set₁ where
  field
    Carrier       : Set
    _∙_           : Carrier → Carrier → Carrier
    isSemilattice : IsSemilattice _∙_

mkDriftSemilattice : ∀ (n : ℕ) → DriftSemilattice n
mkDriftSemilattice n = record
  { Carrier       = Dist n
  ; _∙_           = λ x y → _∧_ {n} x y
  ; isSemilattice = isDriftSemilattice {n}
  }

------------------------------------------------------------------------
-- Join-side semilattice
------------------------------------------------------------------------

isJoinSemilattice : ∀ {n : ℕ} → IsSemilattice (_∨_ {n})
isJoinSemilattice {n} = record
  { assoc      = sound-join-assoc  {n}
  ; comm       = sound-join-comm   {n}
  ; idempotent = sound-join-idempotent {n}
  }

record JoinSemilattice (n : ℕ) : Set₁ where
  field
    Carrier       : Set
    _∙_           : Carrier → Carrier → Carrier
    isSemilattice : IsSemilattice _∙_

mkJoinSemilattice : ∀ (n : ℕ) → JoinSemilattice n
mkJoinSemilattice n = record
  { Carrier       = Dist n
  ; _∙_           = λ x y → _∨_ {n} x y
  ; isSemilattice = isJoinSemilattice {n}
  }