-- src/Structures/S01_BooleanCore/Step02_VectorOperations.agda
{-# OPTIONS --safe #-}

-- | Step 02: Boolean Vectors with Component-wise Operations
-- |
-- | Purpose:
-- |   Construct n-dimensional Boolean spaces ("distinction vectors")
-- |   as Vec Bool n, where Bool is the two-valued algebra derived
-- |   from D₀ (Step01).
-- |
-- | Method:
-- |   Define component-wise logical operations (∧, ∨, not) lifted
-- |   from Step01 to vectors using zipWith and recursion.
-- |
-- | Guarantee:
-- |   All vector operations inherit the soundness of the scalar
-- |   Boolean laws proven in Step01. Thus the multi-dimensional
-- |   case is a direct extension of the 1-dimensional case.

module Structures.S01_BooleanCore.Step02_VectorOperations where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; zipWith)

open import Structures.S01_BooleanCore.Step01_BooleanFoundation

------------------------------------------------------------------------
-- DISTINCTION VECTORS: Multi-dimensional Boolean Spaces
------------------------------------------------------------------------

-- | A distinction is an n-dimensional Boolean vector.
-- | Each component represents a polar choice (marked/unmarked).
Dist : ℕ → Set
Dist n = Vec Bool n

-- | Drift: component-wise Boolean AND.
-- | Interpreted as "both conditions must hold simultaneously".
drift : ∀ {n} → Dist n → Dist n → Dist n
drift = zipWith _∧_

-- | Join: component-wise Boolean OR.
-- | Interpreted as "either condition can hold".
join : ∀ {n} → Dist n → Dist n → Dist n
join = zipWith _∨_

-- | Negation: component-wise Boolean NOT.
-- | Interpreted as "flip all polar choices".
neg : ∀ {n} → Dist n → Dist n
neg []       = []
neg (x ∷ xs) = not x ∷ neg xs

-- | All-true vector: identity element for drift.
all-true : ∀ n → Dist n
all-true zero    = []
all-true (suc n) = true ∷ all-true n

-- | All-false vector: absorbing element for drift.
all-false : ∀ n → Dist n
all-false zero    = []
all-false (suc n) = false ∷ all-false n
