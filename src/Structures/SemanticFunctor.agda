module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
open import Data.List using (_∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)  -- Import Bool constructors

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
-- Helper lemmas: explicit connection between irreducible? and T
------------------------------------------------------------------------

-- If irreducible, then T advances by 1
T-irreducible : ∀ {n} (h : History n) (d : Dist n) → 
                irreducible? d h ≡ true → T (d ∷ h) ≡ suc (T h)
T-irreducible h d irred-true with irreducible? d h
... | true  = refl
... | false = 
  -- Contradiction: irreducible? d h ≡ true but with-clause says false
  -- This case is impossible, but Agda needs explicit proof
  false-not-true irred-true
  where
    false-not-true : false ≡ true → T (d ∷ h) ≡ suc (T h)
    false-not-true ()

-- If reducible, then T stays same
T-reducible : ∀ {n} (h : History n) (d : Dist n) → 
              irreducible? d h ≡ false → T (d ∷ h) ≡ T h
T-reducible h d irred-false with irreducible? d h
... | true  = 
  -- Contradiction case
  true-not-false irred-false
  where
    true-not-false : true ≡ false → T (d ∷ h) ≡ T h
    true-not-false ()
... | false = refl

------------------------------------------------------------------------
-- Clean Properties: Now with explicit lemmas!
------------------------------------------------------------------------

-- Temporal gap is 0 or 1 (from irreducibility)
gap-0-or-1 : ∀ {n} (h : History n) (d : Dist n) → 
             (temporalGap h d ≡ zero) ⊎ (temporalGap h d ≡ suc zero)
gap-0-or-1 h d with irreducible? d h in eq
... | true  = 
  -- Use T-irreducible lemma
  inj₂ (trans 
         (cong (λ x → x ∸ T h) (T-irreducible h d eq))
         (Data.Nat.Properties.+-∸-comm 1 (≤-refl)))
  where open import Data.Nat.Properties using (+-∸-comm; ≤-refl)
... | false = 
  -- Use T-reducible lemma  
  inj₁ (trans 
         (cong (λ x → x ∸ T h) (T-reducible h d eq))
         (Data.Nat.Properties.n∸n≡0 (T h)))
  where open import Data.Nat.Properties using (n∸n≡0)

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
  +-assoc x (temporalGap h d₁) (temporalGap (d₁ ∷ h) d₂)

------------------------------------------------------------------------
-- Bridge to CutCat: Direct correspondence
------------------------------------------------------------------------

-- Temporal stages correspond to CutCat objects
toStage : ∀ {n} → History n → C.Category.Obj C.CutCat  
toStage h = semanticTime h

-- Helper: n ≤ suc n using CutCat constructors
n≤suc-n : ∀ n → n C.≤ suc n
n≤suc-n zero    = C.z≤n
n≤suc-n (suc n) = C.s≤s (n≤suc-n n)

-- Temporal progression corresponds to CutCat morphism
toMorphism : ∀ {n} (h : History n) (d : Dist n) →
             toStage h C.≤ toStage (d ∷ h)
toMorphism h d with irreducible? d h
... | true  = n≤suc-n (semanticTime h)
... | false = C.refl≤ (semanticTime h)

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
------------------------------------------------------------------------
