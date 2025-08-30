{-# OPTIONS --safe #-}

-- | Step 09: Semantic Time Functor
-- | Build temporal structure from distinction sequences and
-- | show functoriality of time-indexed evolution.
module Structures.S02_OrderCategories.Step09_SemanticTimeFunctor where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

-- Our booleans
open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool; true; false)

-- Distinctions and operations
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist)

-- Category of drift-preserving morphisms
open import Structures.S02_OrderCategories.Step08_CategoryStructure
  using (DriftMorphism; idDrift; composeDrift)
  renaming ( swap₂ to swap₂ )

------------------------------------------------------------------------
-- TEMPORAL SEQUENCES
------------------------------------------------------------------------

-- | A temporal sequence is a time-indexed sequence of distinctions
Sequence : ℕ → ℕ → Set
Sequence n t = Vec (Dist n) t

-- | Temporal evolution: apply a morphism to each time step
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

-- | Composition preservation: evolve (φ ∘ ψ) = evolve φ ∘ evolve ψ
evolve-comp :
  ∀ {ℓ m n t}
  (φ : DriftMorphism m n) (ψ : DriftMorphism ℓ m)
  (seq : Sequence ℓ t) →
  evolve (composeDrift φ ψ) seq ≡ evolve φ (evolve ψ seq)
evolve-comp φ ψ []       = refl
evolve-comp φ ψ (d ∷ ds) =
  -- heads are definitionally equal: f (φ ∘ ψ) d  ≡  f φ (f ψ d)
  cong (λ xs → DriftMorphism.f φ (DriftMorphism.f ψ d) ∷ xs)
      (evolve-comp φ ψ ds)

------------------------------------------------------------------------
-- TIME FUNCTOR
------------------------------------------------------------------------

record TimeFunctor : Set₁ where
  field
    F-mor  : ∀ {m n t} → DriftMorphism m n → (Sequence m t → Sequence n t)
    F-id   : ∀ {n t} (seq : Sequence n t) → F-mor idDrift seq ≡ seq
    F-comp :
      ∀ {ℓ m n t} (φ : DriftMorphism m n) (ψ : DriftMorphism ℓ m) (seq : Sequence ℓ t) →
      F-mor (composeDrift φ ψ) seq ≡ F-mor φ (F-mor ψ seq)

timeF : TimeFunctor
timeF = record
  { F-mor  = evolve
  ; F-id   = evolve-id
  ; F-comp = evolve-comp
  }

------------------------------------------------------------------------
-- EXAMPLE: TEMPORAL SWAP
------------------------------------------------------------------------

example-seq : Sequence (suc (suc zero)) (suc (suc (suc zero)))
example-seq =
  (true  ∷ false ∷ []) ∷
  (false ∷ true  ∷ []) ∷
  (true  ∷ true  ∷ []) ∷ []

swapped-seq : Sequence (suc (suc zero)) (suc (suc (suc zero)))
swapped-seq = TimeFunctor.F-mor timeF swap₂ example-seq

swap-result :
  swapped-seq ≡
  ((false ∷ true  ∷ []) ∷
   (true  ∷ false ∷ []) ∷
   (true  ∷ true  ∷ []) ∷ [])
swap-result = refl