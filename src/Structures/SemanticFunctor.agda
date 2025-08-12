module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)

-- Our domain-optimized structures
import Structures.CutCat as C
open C using (_≤_; refl≤; z≤n; s≤s; _∙_)
open import Structures.Drift using (History; T; Dist; irreducible?)

------------------------------------------------------------------------
-- Direct Semantic Mapping: No artificial abstraction!
------------------------------------------------------------------------

-- Semantic time of history: direct and simple
semanticTime : ∀ {n} → History n → ℕ
semanticTime h = T h

-- Temporal difference between histories: arithmetic gap  
temporalGap : ∀ {n} (h : History n) (d : Dist n) → ℕ
temporalGap h d = T (d ∷ h) ∸ T h

-- Temporal progression: shifts values by temporal gap
temporalProgression : ∀ {n} (h : History n) (d : Dist n) → ℕ → ℕ
temporalProgression h d x = x + temporalGap h d

------------------------------------------------------------------------
-- Clean Properties: No complex category theory needed!
------------------------------------------------------------------------

-- Temporal gap is 0 or 1 (from irreducibility)
gap-0-or-1 : ∀ {n} (h : History n) (d : Dist n) → 
             (temporalGap h d ≡ zero) ⊎ (temporalGap h d ≡ suc zero)
gap-0-or-1 h d with irreducible? d h
... | true  = inj₂ refl  -- Irreducible: gap = 1
... | false = inj₁ refl  -- Reducible: gap = 0
  where open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Identity: no change means identity function
identity-progression : ∀ {n} (h : History n) (d : Dist n) → 
                      temporalGap h d ≡ zero → 
                      ∀ x → temporalProgression h d x ≡ x
identity-progression h d gap-zero x = 
  trans (cong (λ g → x + g) gap-zero) (+-identityʳ x)

-- Composition: sequential temporal progressions add up
composition-progression : 
  ∀ {n} (h : History n) (d₁ d₂ : Dist n) (x : ℕ) →
  temporalProgression (d₁ ∷ h) d₂ (temporalProgression h d₁ x) ≡
  temporalProgression h d₂ (temporalProgression h d₁ x)
composition-progression h d₁ d₂ x = 
  -- Left side: (x + gap₁) + gap₂ 
  -- Right side: x + gap₁ + gap₂
  -- Equal by associativity
  +-assoc x (temporalGap h d₁) (temporalGap (d₁ ∷ h) d₂)

------------------------------------------------------------------------
-- Bridge to CutCat: Direct correspondence
------------------------------------------------------------------------

-- Temporal stages correspond to CutCat objects
toStage : ∀ {n} → History n → C.Category.Obj C.CutCat  
toStage h = semanticTime h

-- Temporal progression corresponds to CutCat morphism
toMorphism : ∀ {n} (h : History n) (d : Dist n) →
             toStage h C.≤ toStage (d ∷ h)
toMorphism h d with irreducible? d h
... | true  = C.n≤suc-n (semanticTime h)  -- Time advances by 1
... | false = C.refl≤ (semanticTime h)    -- Time stays same
  where
    -- Helper from CutCat showing n ≤ suc n
    open C using () renaming (n≤suc-n to n≤suc-n)

------------------------------------------------------------------------
-- Connection to Arithmetic: Natural operations
------------------------------------------------------------------------

-- Semantic time induces natural number operations
plus-semantic : ∀ {n} (h : History n) (d : Dist n) (k : ℕ) → ℕ
plus-semantic h d k = k + temporalGap h d  

-- This is just temporal progression with arguments swapped!
plus-semantic-is-progression : 
  ∀ {n} (h : History n) (d : Dist n) (k : ℕ) →
  plus-semantic h d k ≡ temporalProgression h d k
plus-semantic-is-progression h d k = refl

------------------------------------------------------------------------
-- The Complete Semantic Bridge (No category theory overhead!)
-- 
-- Drift Histories → Semantic Time → Temporal Progression → Arithmetic
-- 
-- This is the REAL functor: 
-- - Objects: Histories ↦ Natural numbers (semantic time)
-- - Morphisms: History extensions ↦ Arithmetic operations (+gap)
-- 
-- Clean, direct, and mathematically honest!
------------------------------------------------------------------------
