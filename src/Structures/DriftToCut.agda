module Structures.DriftToCut where

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; suc)  -- Added: suc
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- Import all needed constructors from CutCat at the top level
open import Structures.CutCat using (_≤_; refl≤; s≤s; z≤n; Category; CutCat)  
open import Structures.Drift using (History; T; Dist; irreducible?)

------------------------------------------------------------------------
-- Bridge: Semantic Time induces objects in CutCat
------------------------------------------------------------------------

-- Semantic time of history gives CutCat object
semanticTimeObject : ∀ {n} → History n → Category.Obj CutCat
semanticTimeObject h = T h

-- Helper: n ≤ suc n using CutCat constructors
n≤suc-n : ∀ n → n ≤ suc n
n≤suc-n zero    = z≤n
n≤suc-n (suc n) = s≤s (n≤suc-n n)

-- T-monotonic using CutCat's ≤ relation
T-monotonic-CutCat : ∀ {n} (h : History n) (d : Dist n) → T h ≤ T (d ∷ h)
T-monotonic-CutCat h d with irreducible? d h
... | true  = n≤suc-n (T h)  -- T (d ∷ h) = suc (T h), so T h ≤ suc (T h)
... | false = refl≤ (T h)    -- T (d ∷ h) = T h, so T h ≤ T h

-- History extension induces CutCat morphism via monotonicity
historyExtension→Morphism : 
  ∀ {n} (h : History n) (d : Dist n) →
  Category.Hom CutCat (semanticTimeObject h) (semanticTimeObject (d ∷ h))
historyExtension→Morphism h d = T-monotonic-CutCat h d

-- This establishes the conceptual bridge:
-- Histories with their semantic time structure → CutCat temporal progression
