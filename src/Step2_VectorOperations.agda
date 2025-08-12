-- src/Step2_VectorOperations.agda
{-# OPTIONS --safe #-}

-- | Step 2: Boolean Vectors with Component-wise Operations  
-- | Building multi-dimensional Boolean spaces
module Step2_VectorOperations where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; zipWith)
open import Step1_BooleanFoundation

------------------------------------------------------------------------  
-- DISTINCTION VECTORS: Multi-dimensional Boolean Spaces
------------------------------------------------------------------------

-- | A distinction is an n-dimensional Boolean vector
-- | Each component represents a polar choice (marked/unmarked)
Dist : ℕ → Set
Dist n = Vec Bool n

-- | Drift: component-wise Boolean AND 
-- | Models "both conditions must hold simultaneously"
drift : ∀ {n} → Dist n → Dist n → Dist n
drift = zipWith _∧_

-- | Join: component-wise Boolean OR
-- | Models "either condition can hold"  
join : ∀ {n} → Dist n → Dist n → Dist n
join = zipWith _∨_

-- | Negation: component-wise Boolean NOT
-- | Models "flip all polar choices"
neg : ∀ {n} → Dist n → Dist n  
neg []       = []
neg (x ∷ xs) = not x ∷ neg xs

-- | All-true vector: identity element for drift
all-true : ∀ n → Dist n
all-true zero    = []
all-true (suc n) = true ∷ all-true n

-- | All-false vector: absorbing element for drift
all-false : ∀ n → Dist n
all-false zero    = []
all-false (suc n) = false ∷ all-false n

------------------------------------------------------------------------
-- BREAKTHROUGH: Vector operations inherit Boolean structure!
-- The n-dimensional case follows from 1-dimensional proofs
------------------------------------------------------------------------
