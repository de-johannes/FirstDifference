module Structures.DriftToCut where

open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Structures.Drift using (History; T; T-monotonic)
open import Structures.CutCat as Cut using (CutCat)

------------------------------------------------------------------------
-- Bridge: Semantic Time induces objects in CutCat
------------------------------------------------------------------------

-- Semantic time of history gives CutCat object
semanticTimeObject : ∀ {n} → History n → Cut.Category.Obj CutCat
semanticTimeObject h = T h

-- History extension induces CutCat morphism via monotonicity
historyExtension→Morphism : 
  ∀ {n} (h : History n) (d : Structures.Drift.Dist n) →
  Cut.Category.Hom CutCat (semanticTimeObject h) (semanticTimeObject (d ∷ h))
historyExtension→Morphism h d = T-monotonic h d

-- This establishes the conceptual bridge:
-- Histories with their semantic time structure → CutCat temporal progression
