{-# OPTIONS --safe #-}

-- | Step 05: Semilattice
-- |
-- | Purpose:
-- |   Provide semilattice certificates on Dist-vectors for the two
-- |   operations `drift` (meet-like) and `join` (join-like).
-- |
-- | Method:
-- |   Reuse:
-- |     • Associativity / Commutativity: from Step02_VectorOperations_Soundness
-- |     • Idempotence:                   from Step03_AlgebraLaws_Soundness
-- |
-- | Guarantee:
-- |   All fields are inhabited by previously verified proofs; no new axioms.
-- |
-- | Notes:
-- |   Bounds (⊥/⊤) are intentionally not part of this API; focus is on laws.

module Structures.S02_OrderCategories.Step05_Semilattice where

------------------------------------------------------------------------
-- Imports
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Dist, operations
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join)

-- Assoc / Comm (vector-ops soundness)
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  using ( drift-assoc
        ; drift-comm
        ; join-assoc
        ; join-comm)

-- Idempotence (soundness layer)
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-idempotent
        ; sound-join-idempotent)

------------------------------------------------------------------------
-- Semilattice record (minimal; no external theory)
------------------------------------------------------------------------

record IsSemilattice {ℓ : Level} {A : Set ℓ} (_∙_ : A → A → A) : Set ℓ where
  field
    assoc      : ∀ x y z → _∙_ x (_∙_ y z) ≡ _∙_ (_∙_ x y) z
    comm       : ∀ x y   → _∙_ x y ≡ _∙_ y x
    idempotent : ∀ x     → _∙_ x x ≡ x

------------------------------------------------------------------------
-- Drift-side semilattice
------------------------------------------------------------------------

isDriftSemilattice : ∀ {n : ℕ} → IsSemilattice (drift {n})
isDriftSemilattice {n} = record
  { assoc      = drift-assoc {n}
  ; comm       = drift-comm  {n}
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
  ; _∙_           = λ x y → drift {n} x y
  ; isSemilattice = isDriftSemilattice {n}
  }

------------------------------------------------------------------------
-- Join-side semilattice
------------------------------------------------------------------------

isJoinSemilattice : ∀ {n : ℕ} → IsSemilattice (join {n})
isJoinSemilattice {n} = record
  { assoc      = join-assoc {n}
  ; comm       = join-comm  {n}
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
  ; _∙_           = λ x y → join {n} x y
  ; isSemilattice = isJoinSemilattice {n}
  }
