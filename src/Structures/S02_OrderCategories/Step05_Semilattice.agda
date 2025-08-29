{-# OPTIONS --safe #-}

-- | Step 05: Semilattice
-- |
-- | Purpose:
-- |   Provide meet/join semilattice certificates on Dist-vectors, reusing
-- |   drift/join and their verified laws.
-- |
-- | Method:
-- |   Reuse of Step02/03 results:
-- |     • operations: drift, join (from Step02)
-- |     • vector laws: drift-assoc/comm, join-assoc/comm (from Step02 soundness)
-- |     • soundness: idempotence via sound-* wrappers (from Step03 soundness)
-- |
-- | Guarantee:
-- |   All fields are inhabited by existing proofs; no new axioms or re-proofs.
-- |
-- | Notes:
-- |   Bounds (⊥/⊤) are handled in earlier/later steps; Step05 focuses on the
-- |   semilattice laws only.

module Structures.S02_OrderCategories.Step05_Semilattice where

------------------------------------------------------------------------
-- Imports
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Core ops on distinction vectors
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join)

-- Vector-level algebraic laws (certificates)
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  using ( drift-assoc
        ; drift-comm
        ; join-assoc
        ; join-comm)

-- Soundness wrappers (idempotence)
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-idempotent
        ; sound-join-idempotent)

------------------------------------------------------------------------
-- Public API: operations aliases
------------------------------------------------------------------------

infixl 6 _∧_ _∨_

-- Meet-like operation (alias for drift)
_∧_ : ∀ {n : ℕ} → Dist n → Dist n → Dist n
_∧_ = drift

-- Join-like operation (alias for join)
_∨_ : ∀ {n : ℕ} → Dist n → Dist n → Dist n
_∨_ = join

------------------------------------------------------------------------
-- Semilattice records (minimal, no external theory)
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
  { assoc      = drift-assoc {n}
  ; comm       = drift-comm {n}
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
  { assoc      = join-assoc {n}
  ; comm       = join-comm {n}
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