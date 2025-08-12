{-# OPTIONS --safe #-}

-- | Semantic Functor: bridges drift structures to category theory
-- | This module shows how semantic time induces categorical structure
module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
-- FIX: Import additional properties we need
open import Data.Nat.Properties using (+-assoc; +-identityʳ; n∸n≡0; m+n∸n≡m)
open import Data.List using (_∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- Qualified imports to avoid naming conflicts
import Structures.CutCat as C
open C using (_≤_; refl≤; z≤n; s≤s)
open import Structures.Drift using (History; T; Dist; irreducible?)

------------------------------------------------------------------------
-- Helper lemmas defined at module level (better scoping)
------------------------------------------------------------------------

-- | Helper: suc n ∸ n ≡ 1 (defined at module level for proper scoping)
suc∸n≡1 : ∀ n → suc n ∸ n ≡ suc zero
suc∸n≡1 n = m+n∸n≡m 1 n
-- This uses the standard library lemma m+n∸n≡m with m = 1

------------------------------------------------------------------------
-- Semantic mapping functions
------------------------------------------------------------------------

-- | Extract semantic time from history: direct mapping to ℕ
semanticTime : ∀ {n} → History n → ℕ
semanticTime h = T h

-- | Temporal gap: how much semantic time advances with new distinction
temporalGap : ∀ {n} (h : History n) (d : Dist n) → ℕ
temporalGap h d = T (d ∷ h) ∸ T h

-- | Temporal progression: advance a value by the temporal gap
-- | This models how values evolve with semantic time
temporalProgression : ∀ {n} (h : History n) (d : Dist n) → ℕ → ℕ
temporalProgression h d x = x + temporalGap h d

------------------------------------------------------------------------
-- Properties and lemmas about semantic time
------------------------------------------------------------------------

-- | Helper type for case analysis on Boolean values
BoolType : Bool → Set
BoolType true  = ⊤
BoolType false = ⊥

-- | Key lemma: semantic time behavior depends on irreducibility
-- | This gives us precise control over when T advances
T-behavior : ∀ {n} (h : History n) (d : Dist n) → 
             (irreducible? d h ≡ true → T (d ∷ h) ≡ suc (T h)) ×
             (irreducible? d h ≡ false → T (d ∷ h) ≡ T h)
T-behavior h d = (case-irreducible , case-reducible)
  where
    case-irreducible : irreducible? d h ≡ true → T (d ∷ h) ≡ suc (T h)
    case-irreducible eq with irreducible? d h
    ... | true  = refl
    ... | false = ⊥-elim (subst BoolType eq tt)

    case-reducible : irreducible? d h ≡ false → T (d ∷ h) ≡ T h  
    case-reducible eq with irreducible? d h
    ... | false = refl
    ... | true  = ⊥-elim (subst (λ x → BoolType (not x)) eq tt)

-- | Extract the irreducible case proof
T-irreducible : ∀ {n} (h : History n) (d : Dist n) → 
                irreducible? d h ≡ true → T (d ∷ h) ≡ suc (T h)
T-irreducible h d = proj₁ (T-behavior h d)

-- | Extract the reducible case proof  
T-reducible : ∀ {n} (h : History n) (d : Dist n) → 
              irreducible? d h ≡ false → T (d ∷ h) ≡ T h
T-reducible h d = proj₂ (T-behavior h d)

-- | Temporal gap is always 0 or 1 (follows from irreducibility)
-- | This captures the discrete nature of semantic time advancement
-- FIX: Now uses the properly scoped helper function
gap-binary : ∀ {n} (h : History n) (d : Dist n) → 
             (temporalGap h d ≡ zero) ⊎ (temporalGap h d ≡ suc zero)
gap-binary h d with irreducible? d h
... | true  = inj₂ (suc∸n≡1 (T h))  -- Now properly in scope
... | false = inj₁ (n∸n≡0 (T h))

-- | Identity progression: no temporal gap means identity function
identity-preservation : ∀ {n} (h : History n) (d : Dist n) → 
                       temporalGap h d ≡ zero → 
                       ∀ x → temporalProgression h d x ≡ x
identity-preservation h d gap-zero x = 
  trans (cong (λ g → x + g) gap-zero) (+-identityʳ x)

------------------------------------------------------------------------
-- Bridge to CutCat: Functorial mapping
------------------------------------------------------------------------

-- | Map histories to CutCat objects via their semantic time
toStage : ∀ {n} → History n → C.Category.Obj C.CutCat  
toStage h = semanticTime h

-- | Helper: natural proof that n ≤ suc n
n≤suc-n : ∀ n → n C.≤ suc n
n≤suc-n zero    = C.z≤n
n≤suc-n (suc n) = C.s≤s (n≤suc-n n)

-- | Map history extensions to CutCat morphisms
-- | This shows how adding distinctions induces temporal progression
toMorphism : ∀ {n} (h : History n) (d : Dist n) →
             toStage h C.≤ toStage (d ∷ h)
toMorphism h d with irreducible? d h
... | true  = n≤suc-n (semanticTime h)  -- Time advances
... | false = C.refl≤ (semanticTime h)   -- Time stays constant

------------------------------------------------------------------------
-- Additional utility functions using the product type
------------------------------------------------------------------------

-- | Combine temporal progressions: both gap and progression in one
temporalAnalysis : ∀ {n} (h : History n) (d : Dist n) → 
                   ℕ × (ℕ → ℕ)
temporalAnalysis h d = (temporalGap h d , temporalProgression h d)

-- | Extract gap from analysis
getGap : ∀ {n} (h : History n) (d : Dist n) → ℕ
getGap h d = proj₁ (temporalAnalysis h d)

-- | Extract progression function from analysis  
getProgression : ∀ {n} (h : History n) (d : Dist n) → ℕ → ℕ
getProgression h d = proj₂ (temporalAnalysis h d)

------------------------------------------------------------------------
-- Summary: This establishes the bridge between:
-- • Drift operations (Structures.Drift)
-- • Temporal progression (CutCat) 
-- • Semantic time as a functor from distinction processes to ℕ
-- • Standard library integration for arithmetic properties
------------------------------------------------------------------------
