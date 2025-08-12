{-# OPTIONS --safe #-}

-- | Semantic Functor: bridges drift structures to category theory
-- | This module shows how semantic time induces categorical structure
module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; n∸n≡0)
open import Data.List using (_∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

-- Qualified imports to avoid naming conflicts
import Structures.CutCat as C
open C using (_≤_; refl≤; z≤n; s≤s)
open import Structures.Drift using (History; T; Dist; irreducible?)

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

-- | Temporal gap is always 0 or 1 (follows from irreducibility)
-- | This captures the discrete nature of semantic time advancement
gap-binary : ∀ {n} (h : History n) (d : Dist n) → 
             (temporalGap h d ≡ zero) ⊎ (temporalGap h d ≡ suc zero)
gap-binary h d with irreducible? d h
... | true  = inj₂ (suc∸n≡1 (T h))
... | false = inj₁ (n∸n≡0 (T h))
  where
    -- Helper: suc n ∸ n ≡ 1
    suc∸n≡1 : ∀ n → suc n ∸ n ≡ suc zero
    suc∸n≡1 zero = refl
    suc∸n≡1 (suc n) = suc∸n≡1 n

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
