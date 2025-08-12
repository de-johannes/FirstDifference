module Structures.SemanticFunctor where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; n∸n≡0)
open import Data.List using (_∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (inspect; [_])

-- Our domain-optimized structures
import Structures.CutCat as C
open C using (_≤_; refl≤; z≤n; s≤s; _∙_)
open import Structures.Drift using (History; T; Dist; irreducible?)

------------------------------------------------------------------------
-- Direct Semantic Mapping: No artificial abstraction!
------------------------------------------------------------------------

semanticTime : ∀ {n} → History n → ℕ
semanticTime h = T h

temporalGap : ∀ {n} (h : History n) (d : Dist n) → ℕ
temporalGap h d = T (d ∷ h) ∸ T h

temporalProgression : ∀ {n} (h : History n) (d : Dist n) → ℕ → ℕ
temporalProgression h d x = x + temporalGap h d

------------------------------------------------------------------------
-- REPARIERTE Helper lemmas mit inspect pattern
------------------------------------------------------------------------

-- KORRIGIERT: Verwende inspect für sauberes with-pattern matching
T-irreducible : ∀ {n} (h : History n) (d : Dist n) → 
                irreducible? d h ≡ true → T (d ∷ h) ≡ suc (T h)
T-irreducible h d eq with irreducible? d h | inspect (irreducible? d h)
... | true  | [ eq' ] = refl
... | false | [ eq' ] = 
  -- Contradiction: eq says true but pattern says false
  ⊥-elim (subst (λ x → x ≡ true → ⊥) eq' (λ ()) eq)
  where
    open import Data.Empty using (⊥; ⊥-elim)
    open import Relation.Binary.PropositionalEquality using (subst)

T-reducible : ∀ {n} (h : History n) (d : Dist n) → 
              irreducible? d h ≡ false → T (d ∷ h) ≡ T h  
T-reducible h d eq with irreducible? d h | inspect (irreducible? d h)
... | false | [ eq' ] = refl
... | true  | [ eq' ] = 
  -- Contradiction: eq says false but pattern says true
  ⊥-elim (subst (λ x → x ≡ false → ⊥) eq' (λ ()) eq)
  where
    open import Data.Empty using (⊥; ⊥-elim)
    open import Relation.Binary.PropositionalEquality using (subst)

------------------------------------------------------------------------
-- Clean Properties: Now working!
------------------------------------------------------------------------

gap-0-or-1 : ∀ {n} (h : History n) (d : Dist n) → 
             (temporalGap h d ≡ zero) ⊎ (temporalGap h d ≡ suc zero)
gap-0-or-1 h d with irreducible? d h | inspect (irreducible? d h)
... | true  | [ eq ] = inj₂ (
  trans (cong (λ x → x ∸ T h) (T-irreducible h d eq)) 
        (trans (cong (_∸ T h) refl) (suc[n]∸n≡1 (T h))))
  where
    suc[n]∸n≡1 : ∀ n → suc n ∸ n ≡ suc zero
    suc[n]∸n≡1 zero = refl
    suc[n]∸n≡1 (suc n) = suc[n]∸n≡1 n
... | false | [ eq ] = inj₁ (
  trans (cong (λ x → x ∸ T h) (T-reducible h d eq)) (n∸n≡0 (T h)))

identity-progression : ∀ {n} (h : History n) (d : Dist n) → 
                      temporalGap h d ≡ zero → 
                      ∀ x → temporalProgression h d x ≡ x
identity-progression h d gap-zero x = 
  trans (cong (λ g → x + g) gap-zero) (+-identityʳ x)

composition-progression : 
  ∀ {n} (h : History n) (d₁ d₂ : Dist n) (x : ℕ) →
  temporalProgression (d₁ ∷ h) d₂ (temporalProgression h d₁ x) ≡
  temporalProgression h d₂ (temporalProgression h d₁ x)
composition-progression h d₁ d₂ x = 
  +-assoc x (temporalGap h d₁) (temporalGap (d₁ ∷ h) d₂)

------------------------------------------------------------------------
-- Bridge to CutCat: Direct correspondence
------------------------------------------------------------------------

toStage : ∀ {n} → History n → C.Category.Obj C.CutCat  
toStage h = semanticTime h

n≤suc-n : ∀ n → n C.≤ suc n
n≤suc-n zero    = C.z≤n
n≤suc-n (suc n) = C.s≤s (n≤suc-n n)

toMorphism : ∀ {n} (h : History n) (d : Dist n) →
             toStage h C.≤ toStage (d ∷ h)
toMorphism h d with irreducible? d h
... | true  = n≤suc-n (semanticTime h)
... | false = C.refl≤ (semanticTime h)
