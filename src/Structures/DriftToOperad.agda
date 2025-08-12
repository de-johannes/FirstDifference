module Structures.DriftToOperad where

open import Agda.Primitive using (lzero)
open import Data.Nat using (ℕ; suc)
open import Structures.Drift using (Dist; drift; T; History; irreducible?)

------------------------------------------------------------------------
-- The Drift operation as the core of the Distinction Operad
------------------------------------------------------------------------

-- The drift operation (conjunction of parents) forms the operadic composition
DriftOperation : ∀ {n} → Dist n → Dist n → Dist n
DriftOperation = drift

-- The Distinction Operad captures the essence of binary drift composition
-- with irreducibility as the admission criterion
record DistinctionOperad (n : ℕ) : Set where
  field
    -- Binary composition via drift
    compose : Dist n → Dist n → Dist n
    -- Admission criterion: must be irreducible given history
    admissible : Dist n → History n → Set
    
  -- Default implementations
  compose = DriftOperation
  admissible d h = irreducible? d h ≡ true where
    open import Data.Bool using (true)
    open import Relation.Binary.PropositionalEquality using (_≡_)

-- This gives the conceptual foundation: 
-- Drift operations → Operadic structure → Hierarchical composition
