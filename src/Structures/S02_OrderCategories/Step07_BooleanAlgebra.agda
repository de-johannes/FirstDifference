{-# OPTIONS --safe #-}

-- | Step 07: Boolean algebra on distinction vectors
-- |
-- | Purpose:
-- |   Extend the bounded lattice with a fixed complement operation
-- |   (component-wise negation) and standard Boolean laws
-- |   (complements, De Morgan, involution).
-- |
-- | Method:
-- |   Reuse machine-checked proofs from earlier steps. No new axioms.

module Structures.S02_OrderCategories.Step07_BooleanAlgebra where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Core types/ops
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; neg; all-false; all-true)

-- Bring the bounded lattice packaging
open import Structures.S02_OrderCategories.Step06_BoundedLattice
  using (BoundedLattice; boundedLatticeᵈ)

-- Vector-level proofs we need
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  using (neg-involutive)
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-complement
        ; sound-join-complement
        ; sound-demorgan-drift-join
        ; sound-demorgan-join-drift
        )

------------------------------------------------------------------------
-- Boolean algebra (bounded lattice + fixed complement)
------------------------------------------------------------------------

record BooleanAlgebra (n : ℕ) : Set where
  field
    base     : BoundedLattice n
    ¬_       : Dist n → Dist n
    -- complement laws
    compl⋀   : ∀ x → (BoundedLattice._⋀_ base) x (¬ x) ≡ BoundedLattice.⊥ base
    compl⋁   : ∀ x → (BoundedLattice._⋁_ base) x (¬ x) ≡ BoundedLattice.⊤ base
    -- De Morgan
    deM⋀     : ∀ x y → ¬ ((BoundedLattice._⋀_ base) x y)
                      ≡ (BoundedLattice._⋁_ base) (¬ x) (¬ y)
    deM⋁     : ∀ x y → ¬ ((BoundedLattice._⋁_ base) x y)
                      ≡ (BoundedLattice._⋀_ base) (¬ x) (¬ y)
    -- involution
    inv¬     : ∀ x → ¬ (¬ x) ≡ x

-- Concrete instance for Dist n
booleanAlgebraᵈ : ∀ {n} → BooleanAlgebra n
booleanAlgebraᵈ {n} = record
  { base   = boundedLatticeᵈ
  ; ¬_     = neg
  ; compl⋀ = λ x → sound-drift-complement x
  ; compl⋁ = λ x → sound-join-complement  x
  ; deM⋀   = λ x y → sound-demorgan-drift-join x y
  ; deM⋁   = λ x y → sound-demorgan-join-drift x y
  ; inv¬   = λ x → neg-involutive x
  }