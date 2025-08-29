{-# OPTIONS --safe #-}

-- | Step 05: Semilattice structure on distinction vectors
-- |
-- | Purpose:
-- |   Package the vector-level Boolean operations into standard
-- |   semilattice interfaces (meet/join), including bounded variants.
-- |   This provides a clean algebraic layer before moving to categories.
-- |
-- | Method:
-- |   Reuse machine-checked laws from Step02/Step03 soundness:
-- |     drift  = component-wise ∧  (meet)
-- |     join   = component-wise ∨  (join)
-- |   Associativity / commutativity / idempotence are already proved.
-- |
-- | Guarantee:
-- |   All fields are inhabited by previously verified proofs (no new axioms).

module Structures.S02_OrderCategories.Step05_Semilattice where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Our Booleans and distinctions
open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool)
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; all-false; all-true)

-- Vector-level laws (certificates)
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  using (drift-assoc; drift-comm; join-assoc; join-comm)
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-idempotent
        ; sound-drift-zeroˡ; drift-zeroʳ
        ; sound-join-idempotent
        ; sound-join-oneˡ; sound-join-oneʳ)

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
