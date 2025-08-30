{-# OPTIONS --safe #-}

-- | Step 07: Boolean Algebra — Soundness Layer
-- |
-- | Purpose:
-- |   Provide soundness certificates (sound-…) for the Boolean algebra
-- |   instance on distinction vectors. No new proofs.

module Structures.S02_OrderCategories.Step07_BooleanAlgebra_Soundness where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Structures.S01_BooleanCore.Step02_VectorOperations using (Dist)
open import Structures.S02_OrderCategories.Step07_BooleanAlgebra
open import Structures.S02_OrderCategories.Step06_BoundedLattice using (BoundedLattice)

------------------------------------------------------------------------
-- Re-export the concrete Boolean algebra instance
------------------------------------------------------------------------

sound-BooleanAlgebra : ∀ {n} → BooleanAlgebra n
sound-BooleanAlgebra {n} = booleanAlgebraᵈ {n}

------------------------------------------------------------------------
-- Aliases for the core laws
------------------------------------------------------------------------

sound-compl⋀ : ∀ {n} (x : Dist n) →
  (BoundedLattice._⋀_ (BooleanAlgebra.base (sound-BooleanAlgebra {n}))) x
    (BooleanAlgebra.¬_ (sound-BooleanAlgebra {n}) x)
  ≡ BoundedLattice.⊥ (BooleanAlgebra.base (sound-BooleanAlgebra {n}))
sound-compl⋀ {n} x =
  BooleanAlgebra.compl⋀ (sound-BooleanAlgebra {n}) x

sound-compl⋁ : ∀ {n} (x : Dist n) →
  (BoundedLattice._⋁_ (BooleanAlgebra.base (sound-BooleanAlgebra {n}))) x
    (BooleanAlgebra.¬_ (sound-BooleanAlgebra {n}) x)
  ≡ BoundedLattice.⊤ (BooleanAlgebra.base (sound-BooleanAlgebra {n}))
sound-compl⋁ {n} x =
  BooleanAlgebra.compl⋁ (sound-BooleanAlgebra {n}) x

sound-deM⋀ : ∀ {n} (x y : Dist n) →
  BooleanAlgebra.¬_ (sound-BooleanAlgebra {n})
    ((BoundedLattice._⋀_ (BooleanAlgebra.base (sound-BooleanAlgebra {n}))) x y)
  ≡ (BoundedLattice._⋁_ (BooleanAlgebra.base (sound-BooleanAlgebra {n})))
      (BooleanAlgebra.¬_ (sound-BooleanAlgebra {n}) x)
      (BooleanAlgebra.¬_ (sound-BooleanAlgebra {n}) y)
sound-deM⋀ {n} x y =
  BooleanAlgebra.deM⋀ (sound-BooleanAlgebra {n}) x y

sound-deM⋁ : ∀ {n} (x y : Dist n) →
  BooleanAlgebra.¬_ (sound-BooleanAlgebra {n})
    ((BoundedLattice._⋁_ (BooleanAlgebra.base (sound-BooleanAlgebra {n}))) x y)
  ≡ (BoundedLattice._⋀_ (BooleanAlgebra.base (sound-BooleanAlgebra {n})))
      (BooleanAlgebra.¬_ (sound-BooleanAlgebra {n}) x)
      (BooleanAlgebra.¬_ (sound-BooleanAlgebra {n}) y)
sound-deM⋁ {n} x y =
  BooleanAlgebra.deM⋁ (sound-BooleanAlgebra {n}) x y

sound-inv¬ : ∀ {n} (x : Dist n) →
  BooleanAlgebra.¬_ (sound-BooleanAlgebra {n})
    (BooleanAlgebra.¬_ (sound-BooleanAlgebra {n}) x) ≡ x
sound-inv¬ {n} x =
  BooleanAlgebra.inv¬ (sound-BooleanAlgebra {n}) x