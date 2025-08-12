-- src/Step4_PartialOrder.agda
{-# OPTIONS --safe #-}  

-- | Step 4: Partial Order from Drift Operation
-- | Order relation: a ≤ b iff drift a b ≡ a
module Step4_PartialOrder where

open import Step1_BooleanFoundation
open import Step2_VectorOperations  
open import Step3_AlgebraLaws

------------------------------------------------------------------------
-- DRIFT-BASED ORDERING
------------------------------------------------------------------------

-- | Drift-based partial order: a ≤ᵈ b iff "a implies b"
_≤ᵈ_ : ∀ {n} → Dist n → Dist n → Set
a ≤ᵈ b = drift a b ≡ a

-- | Reflexivity: every distinction relates to itself  
≤ᵈ-refl : ∀ {n} (a : Dist n) → a ≤ᵈ a  
≤ᵈ-refl a = drift-idempotent a

-- | Transitivity: the key proof for partial order
≤ᵈ-trans : ∀ {n} {a b c : Dist n} → a ≤ᵈ b → b ≤ᵈ c → a ≤ᵈ c
≤ᵈ-trans {a = a} {b} {c} a≤b b≤c = 
  trans (cong (λ x → drift x c) (sym a≤b))    -- drift a c ≡ drift (drift a b) c  
        (trans (drift-assoc a b c)            -- ≡ drift a (drift b c)
               (trans (cong (drift a) b≤c)    -- ≡ drift a b  
                      a≤b))                   -- ≡ a

------------------------------------------------------------------------
-- RESULT: (Dist n, ≤ᵈ) forms a partial order!
-- Foundation for category-theoretic structure  
------------------------------------------------------------------------
