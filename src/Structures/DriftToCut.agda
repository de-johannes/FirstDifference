module Structures.DriftToCut where

open import Data.List using (_∷_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Now both modules use the same ≤ relation - perfect harmony!
open import Structures.CutCat using (Category; CutCat)  
open import Structures.Drift using (History; T; Dist; T-monotonic)

------------------------------------------------------------------------
-- Bridge: Semantic Time induces objects in CutCat
-- No type conversion needed - both use Data.Nat.≤!
------------------------------------------------------------------------

-- Semantic time of history gives CutCat object
semanticTimeObject : ∀ {n} → History n → Category.Obj CutCat
semanticTimeObject h = T h

-- History extension induces CutCat morphism via monotonicity
-- Beautiful: T-monotonic produces exactly the right type!
historyExtension→Morphism : 
  ∀ {n} (h : History n) (d : Dist n) →
  Category.Hom CutCat (semanticTimeObject h) (semanticTimeObject (d ∷ h))
historyExtension→Morphism h d = T-monotonic h d

-- This establishes the conceptual bridge:
-- Histories with their semantic time structure → CutCat temporal progression
-- Clean, direct, no impedance mismatch!
