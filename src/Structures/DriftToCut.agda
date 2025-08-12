module Structures.DriftToCut where

open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- Import ≤ from CutCat, not Data.Nat!
open import Structures.CutCat using (_≤_; Category; CutCat)  
open import Structures.Drift using (History; T; Dist)

------------------------------------------------------------------------
-- Bridge: Semantic Time induces objects in CutCat
------------------------------------------------------------------------

-- Semantic time of history gives CutCat object
semanticTimeObject : ∀ {n} → History n → Category.Obj CutCat
semanticTimeObject h = T h

-- We need T-monotonic that produces CutCat.≤, not Data.Nat.≤
-- So we redefine it here with the correct ≤ relation
T-monotonic-CutCat : ∀ {n} (h : History n) (d : Dist n) → T h ≤ T (d ∷ h)
T-monotonic-CutCat {n} h d with Structures.Drift.irreducible? d h
... | true  = s≤s (refl≤ (T h))  -- T (d ∷ h) = suc (T h)
... | false = refl≤ (T h)        -- T (d ∷ h) = T h
  where
    open import Structures.CutCat using (refl≤; s≤s; z≤n)

-- History extension induces CutCat morphism via monotonicity
historyExtension→Morphism : 
  ∀ {n} (h : History n) (d : Dist n) →
  Category.Hom CutCat (semanticTimeObject h) (semanticTimeObject (d ∷ h))
historyExtension→Morphism h d = T-monotonic-CutCat h d

-- This establishes the conceptual bridge:
-- Histories with their semantic time structure → CutCat temporal progression
