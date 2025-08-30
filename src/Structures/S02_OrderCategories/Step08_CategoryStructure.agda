{-# OPTIONS --safe #-}

-- | Step 08: Category of Drift-Preserving Morphisms
-- |
-- | Purpose:
-- |   Package structure-preserving maps between distinction spaces
-- |   (vectors of Booleans) into a small category:
-- |     • objects  : ℕ  (dimension n ↦ Dist n)
-- |     • morphisms: functions f : Dist m → Dist n
-- |                   that preserve (drift, join, neg)
-- |     • id and ∘ satisfy category laws by definitional equality
-- |
-- | Method:
-- |   Reuse our core Bool/Vec-based definitions (Step01–Step02).
-- |   Proofs below are all by refl or simple congruence.

module Structures.S02_OrderCategories.Step08_CategoryStructure where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

-- Bring our scalar Booleans (no dependency on Data.Bool)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool; true; false)

-- Distinction vectors and operations
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; neg)

------------------------------------------------------------------------
-- Morphisms that preserve the Boolean-vector structure
------------------------------------------------------------------------

record DriftMorphism (m n : ℕ) : Set where
  field
    f              : Dist m → Dist n
    preserves-drift : ∀ a b → f (drift a b) ≡ drift (f a) (f b)
    preserves-join  : ∀ a b → f (join  a b) ≡ join  (f a) (f b)
    preserves-neg   : ∀ a   → f (neg   a) ≡ neg   (f a)

open DriftMorphism public

------------------------------------------------------------------------
-- Identity and composition
------------------------------------------------------------------------

idDrift : ∀ {n} → DriftMorphism n n
idDrift = record
  { f              = id
  ; preserves-drift = λ _ _ → refl
  ; preserves-join  = λ _ _ → refl
  ; preserves-neg   = λ _   → refl
  }

composeDrift : ∀ {ℓ m n} → DriftMorphism m n → DriftMorphism ℓ m → DriftMorphism ℓ n
composeDrift g f = record
  { f = DriftMorphism.f g ∘ DriftMorphism.f f
  ; preserves-drift = λ a b →
      trans (cong (DriftMorphism.f g) (DriftMorphism.preserves-drift f a b))
           (DriftMorphism.preserves-drift g (DriftMorphism.f f a) (DriftMorphism.f f b))
  ; preserves-join  = λ a b →
      trans (cong (DriftMorphism.f g) (DriftMorphism.preserves-join  f a b))
           (DriftMorphism.preserves-join  g (DriftMorphism.f f a) (DriftMorphism.f f b))
  ; preserves-neg   = λ a   →
      trans (cong (DriftMorphism.f g) (DriftMorphism.preserves-neg   f a))
           (DriftMorphism.preserves-neg   g (DriftMorphism.f f a))
  }

------------------------------------------------------------------------
-- Category laws (hold by definitional equality)
------------------------------------------------------------------------

cat-idˡ : ∀ {m n} (φ : DriftMorphism m n) (x : Dist m) →
          DriftMorphism.f (composeDrift idDrift φ) x ≡ DriftMorphism.f φ x
cat-idˡ φ x = refl

cat-idʳ : ∀ {m n} (φ : DriftMorphism m n) (x : Dist m) →
          DriftMorphism.f (composeDrift φ idDrift) x ≡ DriftMorphism.f φ x
cat-idʳ φ x = refl

cat-assoc : ∀ {k ℓ m n}
  (φ : DriftMorphism k ℓ) (ψ : DriftMorphism ℓ m) (χ : DriftMorphism m n) (x : Dist k) →
  DriftMorphism.f (composeDrift (composeDrift χ ψ) φ) x
  ≡
  DriftMorphism.f (composeDrift χ (composeDrift ψ φ)) x
cat-assoc φ ψ χ x = refl

------------------------------------------------------------------------
-- Example: swapping two components (n = 2)
------------------------------------------------------------------------

swap₂ : DriftMorphism (suc (suc zero)) (suc (suc zero))
swap₂ = record
  { f = λ { (a ∷ b ∷ []) → b ∷ a ∷ [] }
  ; preserves-drift = λ where (a₁ ∷ a₂ ∷ []) (b₁ ∷ b₂ ∷ []) → refl
  ; preserves-join  = λ where (a₁ ∷ a₂ ∷ []) (b₁ ∷ b₂ ∷ []) → refl
  ; preserves-neg   = λ where (a  ∷ b  ∷ []) → refl
  }

swap-involution : ∀ (x : Dist (suc (suc zero))) →
  DriftMorphism.f (composeDrift swap₂ swap₂) x ≡ DriftMorphism.f idDrift x
swap-involution (a ∷ b ∷ []) = refl