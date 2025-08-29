{-# OPTIONS --safe #-}

-- | Step 07: Boolean Algebra — Soundness Layer
-- |
-- | Purpose:
-- |   Provide soundness certificates (sound-…) for the Boolean algebra
-- |   instance on distinction vectors, re-exporting complement,
-- |   De Morgan, and involution properties.
-- |
-- | Guarantee:
-- |   No new proofs; only aliasing of verified fields.

module Structures.S02_OrderCategories.Step07_BooleanAlgebra_Soundness where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Core ops
open import Structures.S01_BooleanCore.Step02_VectorOperations using (Dist)

-- Import the Boolean algebra packaging
open import Structures.S02_OrderCategories.Step07_BooleanAlgebra

------------------------------------------------------------------------
-- Boolean algebra soundness (compl, De Morgan, involution)
------------------------------------------------------------------------

sound-booleanAlgebra : ∀ {n} → BooleanAlgebra n
sound-booleanAlgebra = booleanAlgebraᵈ

sound-compl⋀ : ∀ {n} (x : Dist n) →
  (BoundedLattice._⋀_ (BooleanAlgebra.base (sound-booleanAlgebra {n}))) x (BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) x)
  ≡ BoundedLattice.⊥ (BooleanAlgebra.base (sound-booleanAlgebra {n}))
sound-compl⋀ = BooleanAlgebra.compl⋀ (sound-booleanAlgebra _)

sound-compl⋁ : ∀ {n} (x : Dist n) →
  (BoundedLattice._⋁_ (BooleanAlgebra.base (sound-booleanAlgebra {n}))) x (BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) x)
  ≡ BoundedLattice.⊤ (BooleanAlgebra.base (sound-booleanAlgebra {n}))
sound-compl⋁ = BooleanAlgebra.compl⋁ (sound-booleanAlgebra _)

sound-deM⋀ : ∀ {n} (x y : Dist n) →
  BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) ((BoundedLattice._⋀_ (BooleanAlgebra.base (sound-booleanAlgebra {n}))) x y)
  ≡ (BoundedLattice._⋁_ (BooleanAlgebra.base (sound-booleanAlgebra {n}))) (BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) x) (BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) y)
sound-deM⋀ = BooleanAlgebra.deM⋀ (sound-booleanAlgebra _)

sound-deM⋁ : ∀ {n} (x y : Dist n) →
  BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) ((BoundedLattice._⋁_ (BooleanAlgebra.base (sound-booleanAlgebra {n}))) x y)
  ≡ (BoundedLattice._⋀_ (BooleanAlgebra.base (sound-booleanAlgebra {n}))) (BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) x) (BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) y)
sound-deM⋁ = BooleanAlgebra.deM⋁ (sound-booleanAlgebra _)

sound-inv¬ : ∀ {n} (x : Dist n) → BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) (BooleanAlgebra.¬_ (sound-booleanAlgebra {n}) x) ≡ x
sound-inv¬ = BooleanAlgebra.inv¬ (sound-booleanAlgebra _)