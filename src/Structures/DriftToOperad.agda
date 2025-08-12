module Structures.DriftToOperad where

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; true; _≡_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Structures.Drift using (Dist; drift; T; History; irreducible?)

------------------------------------------------------------------------
-- The Drift operation as the core of the Distinction Operad
------------------------------------------------------------------------

-- The drift operation (conjunction of parents) forms the operadic composition
DriftOperation : ∀ {n} → Dist n → Dist n → Dist n
DriftOperation = drift

------------------------------------------------------------------------
-- The Distinction Operad: captures binary drift composition
-- with irreducibility as admission criterion
------------------------------------------------------------------------

record DistinctionOperad (n : ℕ) : Set where
  field
    -- Binary composition operation
    compose : Dist n → Dist n → Dist n
    -- Admission criterion: must be irreducible given history  
    admissible : Dist n → History n → Bool

open DistinctionOperad public

-- Standard implementation using drift operation
standardDistinctionOperad : ∀ n → DistinctionOperad n
standardDistinctionOperad n .compose = DriftOperation
standardDistinctionOperad n .admissible = irreducible?

------------------------------------------------------------------------
-- This gives the conceptual foundation: 
-- Drift operations → Operadic structure → Hierarchical composition
------------------------------------------------------------------------
