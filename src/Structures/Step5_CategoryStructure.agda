{-# OPTIONS --safe #-}

-- | Step 5: Category of Drift-Preserving Morphisms (CORRECT PROOFS)
module Structures.Step5_CategoryStructure where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Function using (id; _∘_)
open import Data.Product using (_×_; _,_)

-- Step imports
open import Structures.01_BooleanCore.Step01_BooleanFoundation
open import Structures.Step2_VectorOperations  
open import Structures.Step3_AlgebraLaws
open import Structures.Step4_PartialOrder

------------------------------------------------------------------------
-- DRIFT MORPHISMS: Structure-Preserving Maps
------------------------------------------------------------------------

record DriftMorphism (m n : ℕ) : Set where
  field
    f : Dist m → Dist n
    preserves-drift : ∀ a b → f (drift a b) ≡ drift (f a) (f b)
    preserves-join  : ∀ a b → f (join a b) ≡ join (f a) (f b)  
    preserves-neg   : ∀ a → f (neg a) ≡ neg (f a)

open DriftMorphism public

------------------------------------------------------------------------
-- IDENTITY: Always works
------------------------------------------------------------------------

idDrift : ∀ {n} → DriftMorphism n n
idDrift = record
  { f = id
  ; preserves-drift = λ _ _ → refl
  ; preserves-join  = λ _ _ → refl
  ; preserves-neg   = λ _ → refl
  }

------------------------------------------------------------------------
-- COMPOSITION: Preserves structure
------------------------------------------------------------------------

composeDrift : ∀ {l m n} → DriftMorphism m n → DriftMorphism l m → DriftMorphism l n
composeDrift g f = record
  { f = DriftMorphism.f g ∘ DriftMorphism.f f
  ; preserves-drift = λ a b → 
      trans (cong (DriftMorphism.f g) (DriftMorphism.preserves-drift f a b))
            (DriftMorphism.preserves-drift g (DriftMorphism.f f a) (DriftMorphism.f f b))
  ; preserves-join = λ a b →
      trans (cong (DriftMorphism.f g) (DriftMorphism.preserves-join f a b))
            (DriftMorphism.preserves-join g (DriftMorphism.f f a) (DriftMorphism.f f b))
  ; preserves-neg = λ a →
      trans (cong (DriftMorphism.f g) (DriftMorphism.preserves-neg f a))
            (DriftMorphism.preserves-neg g (DriftMorphism.f f a))
  }

------------------------------------------------------------------------
-- CATEGORY LAWS: Perfect definitional equality
------------------------------------------------------------------------

drift-cat-idˡ : ∀ {m n} (φ : DriftMorphism m n) → 
                ∀ x → DriftMorphism.f (composeDrift idDrift φ) x ≡ DriftMorphism.f φ x
drift-cat-idˡ φ x = refl

drift-cat-idʳ : ∀ {m n} (φ : DriftMorphism m n) → 
                ∀ x → DriftMorphism.f (composeDrift φ idDrift) x ≡ DriftMorphism.f φ x
drift-cat-idʳ φ x = refl

drift-cat-assoc : ∀ {k l m n} (φ : DriftMorphism k l) (ψ : DriftMorphism l m) (χ : DriftMorphism m n) →
                  ∀ x → DriftMorphism.f (composeDrift (composeDrift χ ψ) φ) x ≡ 
                        DriftMorphism.f (composeDrift χ (composeDrift ψ φ)) x
drift-cat-assoc φ ψ χ x = refl

------------------------------------------------------------------------
-- COMPONENT SWAP: Correct proof by refl
------------------------------------------------------------------------

-- Helper function for swapping
swap-2d : Dist (suc (suc zero)) → Dist (suc (suc zero))
swap-2d (a ∷ b ∷ []) = b ∷ a ∷ []

-- FIXED: The proofs are actually just refl!
swap-preserves-drift : ∀ (v w : Dist (suc (suc zero))) → 
                       swap-2d (drift v w) ≡ drift (swap-2d v) (swap-2d w)
swap-preserves-drift (a₁ ∷ a₂ ∷ []) (b₁ ∷ b₂ ∷ []) = refl

swap-preserves-join : ∀ (v w : Dist (suc (suc zero))) → 
                      swap-2d (join v w) ≡ join (swap-2d v) (swap-2d w)
swap-preserves-join (a₁ ∷ a₂ ∷ []) (b₁ ∷ b₂ ∷ []) = refl

swap-preserves-neg : ∀ (v : Dist (suc (suc zero))) → 
                     swap-2d (neg v) ≡ neg (swap-2d v)
swap-preserves-neg (a ∷ b ∷ []) = refl

-- The swap morphism
swap₀₁ : DriftMorphism (suc (suc zero)) (suc (suc zero))
swap₀₁ = record
  { f = swap-2d
  ; preserves-drift = swap-preserves-drift
  ; preserves-join = swap-preserves-join
  ; preserves-neg = swap-preserves-neg
  }

-- Swap is self-inverse
swap-involution : ∀ x → DriftMorphism.f (composeDrift swap₀₁ swap₀₁) x ≡ DriftMorphism.f idDrift x
swap-involution (a ∷ b ∷ []) = refl

------------------------------------------------------------------------
-- CATEGORICAL STRUCTURE THEOREM
------------------------------------------------------------------------

category-structure-proven : ∀ {l m n} (φ : DriftMorphism m n) (ψ : DriftMorphism l m) →
  (∀ x → DriftMorphism.f (composeDrift idDrift φ) x ≡ DriftMorphism.f φ x) ×
  (∀ x → DriftMorphism.f (composeDrift φ idDrift) x ≡ DriftMorphism.f φ x) ×  
  (∀ {k} (χ : DriftMorphism k l) x → 
    DriftMorphism.f (composeDrift (composeDrift φ ψ) χ) x ≡ 
    DriftMorphism.f (composeDrift φ (composeDrift ψ χ)) x)
category-structure-proven φ ψ = 
  ( drift-cat-idˡ φ
  , drift-cat-idʳ φ
  , λ {k} χ x → drift-cat-assoc χ ψ φ x
  )

-- Core properties
identity-neutral : ∀ {n} (d : Dist n) → DriftMorphism.f idDrift d ≡ d
identity-neutral d = refl

-- Working examples
swap-example : DriftMorphism.f swap₀₁ (true ∷ false ∷ []) ≡ (false ∷ true ∷ [])
swap-example = refl

drift-example : drift (true ∷ false ∷ []) (false ∷ true ∷ []) ≡ (false ∷ false ∷ [])
drift-example = refl

------------------------------------------------------------------------
-- RESULT: Perfect categorical structure!
-- • All proofs work by definitional equality (refl)
-- • Identity and swap morphisms fully functional
-- • Category laws automatically satisfied
-- • Clean, minimal, completely rigorous!
------------------------------------------------------------------------
