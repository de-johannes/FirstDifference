{-# OPTIONS --safe #-}

-- | Step 05: Semilattice
-- |
-- | Purpose:
-- |   Provide meet/join semilattice structures on Dist-vectors, reusing the
-- |   drift/join operations and their previously verified laws.
-- |
-- | Method:
-- |   Reuse of Step02/03 results:
-- |     • operations:    drift, join, all-false, all-true  (from Step02)
-- |     • vector laws:   drift-assoc/comm, join-assoc/comm, drift-zeroʳ (from Step02 soundness)
-- |     • soundness:     idempotence/units/left-zero via sound-* wrappers (from Step03 soundness)
-- |
-- | Guarantee:
-- |   All fields are inhabited by existing proofs; no new axioms or re-proofs.
-- |
-- | Notes:
-- |   Finite families only; avoid builtin Bool. We use Dist-level operations only.

module Structures.S02_OrderCategories.Step05_Semilattice where

------------------------------------------------------------------------
-- Imports
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

-- Natural numbers for vector lengths / indices
open import Data.Nat using (ℕ)

-- Equality
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Core ops on distinction vectors
-- NOTE: `Dist` (type) and its constructor `Dist` are exported under the same name.
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using ( Dist       -- type / constructor
        ; drift
        ; join
        ; all-false
        ; all-true)

-- Vector-level algebraic laws (certificates) — includes right zero for drift
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  using ( drift-assoc
        ; drift-comm
        ; join-assoc
        ; join-comm
        ; drift-zeroʳ)

-- Soundness wrappers (idempotence, units, left zero)
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-idempotent
        ; sound-drift-zeroˡ
        ; sound-join-idempotent
        ; sound-join-oneˡ
        ; sound-join-oneʳ)

------------------------------------------------------------------------
-- Basic aliases (public API convenience)
------------------------------------------------------------------------

infixl 6 _∧_ _∨_

-- Meet-like operation (alias for drift)
_∧_ : ∀ {n : ℕ} → Dist n → Dist n → Dist n
_∧_ = drift

-- Join-like operation (alias for join)
_∨_ : ∀ {n : ℕ} → Dist n → Dist n → Dist n
_∨_ = join

-- Bounds: lift vector-level constants to Dist via the `Dist` constructor
⊥ : ∀ {n : ℕ} → Dist n
⊥ {n} = Dist all-false

⊤ : ∀ {n : ℕ} → Dist n
⊤ {n} = Dist all-true

------------------------------------------------------------------------
-- Law records (local, minimal; no external theory)
------------------------------------------------------------------------

record IsSemilattice {ℓ : Level} {A : Set ℓ} (_∙_ : A → A → A) : Set ℓ where
  field
    assoc      : ∀ x y z → _∙_ x (_∙_ y z) ≡ _∙_ (_∙_ x y) z
    comm       : ∀ x y   → _∙_ x y ≡ _∙_ y x
    idempotent : ∀ x     → _∙_ x x ≡ x

record HasIdentity {ℓ : Level} {A : Set ℓ} (_∙_ : A → A → A) (e : A) : Set ℓ where
  field
    idˡ : ∀ x → _∙_ e x ≡ x
    idʳ : ∀ x → _∙_ x e ≡ x

record HasAbsorber {ℓ : Level} {A : Set ℓ} (_∙_ : A → A → A) (a : A) : Set ℓ where
  field
    absˡ : ∀ x → _∙_ a x ≡ a
    absʳ : ∀ x → _∙_ x a ≡ a

------------------------------------------------------------------------
-- Drift-side semilattice (meet)
------------------------------------------------------------------------

-- All drift-laws bundled in a single certificate for Dist n
isDriftSemilattice : ∀ {n : ℕ} → IsSemilattice (_∧_ {n})
isDriftSemilattice {n} = record
  { assoc      = drift-assoc {n}
  ; comm       = drift-comm {n}
  ; idempotent = sound-drift-idempotent {n}
  }

-- Absorber for drift: ⊥ is absorbing element (both sides)
driftAbsorber : ∀ {n : ℕ} → HasAbsorber (_∧_ {n}) (⊥ {n})
driftAbsorber {n} = record
  { absˡ = sound-drift-zeroˡ {n}
  ; absʳ = drift-zeroʳ       {n}
  }

-- Packaged semilattice structure for a fixed length n
record DriftSemilattice (n : ℕ) : Set₁ where
  field
    Carrier       : Set
    _∙_           : Carrier → Carrier → Carrier
    bottom        : Carrier
    isSemilattice : IsSemilattice _∙_
    hasAbsorber   : HasAbsorber _∙_ bottom

-- Canonical instance on Dist n
mkDriftSemilattice : ∀ (n : ℕ) → DriftSemilattice n
mkDriftSemilattice n = record
  { Carrier       = Dist n
  ; _∙_           = λ x y → _∧_ {n} x y
  ; bottom        = ⊥ {n}
  ; isSemilattice = isDriftSemilattice {n}
  ; hasAbsorber   = driftAbsorber {n}
  }

------------------------------------------------------------------------
-- Join-side semilattice
------------------------------------------------------------------------

-- All join-laws bundled in a single certificate for Dist n
isJoinSemilattice : ∀ {n : ℕ} → IsSemilattice (_∨_ {n})
isJoinSemilattice {n} = record
  { assoc      = join-assoc {n}
  ; comm       = join-comm {n}
  ; idempotent = sound-join-idempotent {n}
  }

-- Identity for join: ⊤ is a (two-sided) identity element
joinIdentity : ∀ {n : ℕ} → HasIdentity (_∨_ {n}) (⊤ {n})
joinIdentity {n} = record
  { idˡ = sound-join-oneˡ {n}
  ; idʳ = sound-join-oneʳ {n}
  }

-- Packaged semilattice structure for a fixed length n
record JoinSemilattice (n : ℕ) : Set₁ where
  field
    Carrier       : Set
    _∙_           : Carrier → Carrier → Carrier
    top           : Carrier
    isSemilattice : IsSemilattice _∙_
    hasIdentity   : HasIdentity _∙_ top

-- Canonical instance on Dist n
mkJoinSemilattice : ∀ (n : ℕ) → JoinSemilattice n
mkJoinSemilattice n = record
  { Carrier       = Dist n
  ; _∙_           = λ x y → _∨_ {n} x y
  ; top           = ⊤ {n}
  ; isSemilattice = isJoinSemilattice {n}
  ; hasIdentity   = joinIdentity {n}
  }