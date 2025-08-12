{-# OPTIONS --safe #-}

-- | Step 6: Semantic Time Functor
-- | Building temporal structure from distinction sequences
module Step6_SemanticTimeFunctor where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function using (id; _∘_)
open import Data.Product using (_×_; _,_)

-- Explizite Importe aller benötigten Module
open import Step1_BooleanFoundation
open import Step2_VectorOperations  
open import Step3_AlgebraLaws
open import Step4_PartialOrder
open import Step5_CategoryStructure

------------------------------------------------------------------------
-- TEMPORAL SEQUENCE TYPE
------------------------------------------------------------------------

-- | A temporal sequence is a time-indexed sequence of distinctions
Sequence : ℕ → ℕ → Set
Sequence n t = Vec (Dist n) t

-- | Temporal evolution: applying a morphism to each time step
evolve : ∀ {m n t} → DriftMorphism m n → Sequence m t → Sequence n t
evolve φ []       = []
evolve φ (d ∷ ds) = DriftMorphism.f φ d ∷ evolve φ ds

------------------------------------------------------------------------
-- FUNCTOR LAWS FOR TEMPORAL EVOLUTION
------------------------------------------------------------------------

-- | Identity preservation: evolving with identity does nothing
evolve-id : ∀ {n t} (seq : Sequence n t) → evolve idDrift seq ≡ seq
evolve-id []       = refl
evolve-id (d ∷ ds) = cong (d ∷_) (evolve-id ds)

-- | Composition preservation: evolving with composition = composing evolutions
evolve-comp : ∀ {l m n t} (φ : DriftMorphism m n) (ψ : DriftMorphism l m) 
              (seq : Sequence l t) →
              evolve (composeDrift φ ψ) seq ≡ evolve φ (evolve ψ seq)
evolve-comp φ ψ []       = refl
evolve-comp φ ψ (d ∷ ds) = cong (_ ∷_) (evolve-comp φ ψ ds)

------------------------------------------------------------------------
-- SEMANTIC TIME STRUCTURE
------------------------------------------------------------------------

-- | Time functor: maps morphisms to sequence transformations
record TimeFunctor : Set₁ where
  field
    -- Functor action on morphisms
    F-mor : ∀ {m n t} → DriftMorphism m n → (Sequence m t → Sequence n t)
    
    -- Functor laws
    F-id  : ∀ {n t} (seq : Sequence n t) → F-mor idDrift seq ≡ seq
    F-comp : ∀ {l m n t} (φ : DriftMorphism m n) (ψ : DriftMorphism l m) 
             (seq : Sequence l t) →
             F-mor (composeDrift φ ψ) seq ≡ F-mor φ (F-mor ψ seq)

-- | The canonical time functor
timeF : TimeFunctor
timeF = record
  { F-mor = evolve
  ; F-id = evolve-id
  ; F-comp = evolve-comp
  }

------------------------------------------------------------------------
-- EXAMPLE: TEMPORAL SWAP
------------------------------------------------------------------------

-- | Example sequence: alternating true/false pattern
example-seq : Sequence (suc (suc zero)) (suc (suc (suc zero)))
example-seq = (true ∷ false ∷ []) ∷ 
              (false ∷ true ∷ []) ∷ 
              (true ∷ true ∷ []) ∷ []

-- | Apply swap to the temporal sequence
swapped-seq : Sequence (suc (suc zero)) (suc (suc (suc zero)))
swapped-seq = TimeFunctor.F-mor timeF swap₀₁ example-seq

-- | The result: components are swapped at each time step
swap-result : swapped-seq ≡ ((false ∷ true ∷ []) ∷ 
                             (true ∷ false ∷ []) ∷ 
                             (true ∷ true ∷ []) ∷ [])
swap-result = refl

------------------------------------------------------------------------
-- RESULT: Time as a functor!
-- • Temporal sequences form the objects
-- • Morphisms act uniformly across time
-- • Functor laws ensure coherent temporal evolution
-- • Foundation for process-based temporal logic
------------------------------------------------------------------------
