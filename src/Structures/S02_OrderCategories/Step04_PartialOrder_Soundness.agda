{-# OPTIONS --safe #-}

-- | Step 04: Drift-Induced Partial Order — Soundness Layer
-- |
-- | Purpose:
-- |   Provide unique "soundness certificates" (sound-…) for all
-- |   properties proven in Step04_PartialOrder. This allows
-- |   `open … public` without name clashes in All.agda.
-- |
-- | Method:
-- |   Each certificate is a direct alias to the corresponding theorem
-- |   in Step04_PartialOrder. No new proofs are introduced here.
-- |
-- | Guarantee:
-- |   Fully machine-checked under --safe. Zero postulates.

module Structures.S02_OrderCategories.Step04_PartialOrder_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Nat using (ℕ)

-- Types and operations on Dist
open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool)
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; neg; all-true; all-false)

-- Properties to be re-exported as soundness certificates
open import Structures.S02_OrderCategories.Step04_PartialOrder

------------------------------------------------------------------------
-- Partial Order: Reflexivity, Antisymmetry, Transitivity
------------------------------------------------------------------------

sound-≤ᵈ-refl : ∀ {n} (a : Dist n) → a ≤ᵈ a
sound-≤ᵈ-refl = ≤ᵈ-refl

sound-≤ᵈ-antisym : ∀ {n} {a b : Dist n} → a ≤ᵈ b → b ≤ᵈ a → a ≡ b
sound-≤ᵈ-antisym = ≤ᵈ-antisym

sound-≤ᵈ-trans : ∀ {n} {a b c : Dist n} → a ≤ᵈ b → b ≤ᵈ c → a ≤ᵈ c
sound-≤ᵈ-trans = ≤ᵈ-trans

------------------------------------------------------------------------
-- Decidability
------------------------------------------------------------------------

sound-≟ᵈ : ∀ {n} → (a b : Dist n) → Dec (a ≡ b)
sound-≟ᵈ = _≟ᵈ_

sound-≤ᵈ-dec : ∀ {n} (a b : Dist n) → Dec (a ≤ᵈ b)
sound-≤ᵈ-dec = ≤ᵈ-dec

sound-≤ᵈ? : ∀ {n} → Dist n → Dist n → Bool
sound-≤ᵈ? = ≤ᵈ?

------------------------------------------------------------------------
-- Bounds (⊥, ⊤) and their order properties
------------------------------------------------------------------------

sound-⊥ᵈ : ∀ {n} → Dist n
sound-⊥ᵈ = ⊥ᵈ

sound-⊥ᵈ-least : ∀ {n} (a : Dist n) → sound-⊥ᵈ ≤ᵈ a
sound-⊥ᵈ-least = ⊥ᵈ-least

sound-⊤ᵈ : ∀ {n} → Dist n
sound-⊤ᵈ = ⊤ᵈ

sound-⊤ᵈ-greatest : ∀ {n} (a : Dist n) → a ≤ᵈ sound-⊤ᵈ
sound-⊤ᵈ-greatest = ⊤ᵈ-greatest

------------------------------------------------------------------------
-- Lattice properties: Meet (GLB) and Join (LUB)
------------------------------------------------------------------------

sound-meet≤₁ : ∀ {n} (a b : Dist n) → drift a b ≤ᵈ a
sound-meet≤₁ = meet≤₁

sound-meet≤₂ : ∀ {n} (a b : Dist n) → drift a b ≤ᵈ b
sound-meet≤₂ = meet≤₂

sound-glb-≤ᵈ :
  ∀ {n} {a b c : Dist n} → c ≤ᵈ a → c ≤ᵈ b → c ≤ᵈ drift a b
sound-glb-≤ᵈ = glb-≤ᵈ

sound-ub-join₁ : ∀ {n} (a b : Dist n) → a ≤ᵈ join a b
sound-ub-join₁ = ub-join₁

sound-ub-join₂ : ∀ {n} (a b : Dist n) → b ≤ᵈ join a b
sound-ub-join₂ = ub-join₂

sound-lub-≤ᵈ :
  ∀ {n} {a b c : Dist n} → a ≤ᵈ c → b ≤ᵈ c → join a b ≤ᵈ c
sound-lub-≤ᵈ = lub-≤ᵈ

------------------------------------------------------------------------
-- Complements & De Morgan (vector form)
------------------------------------------------------------------------

sound-compl-meet-bot : ∀ {n} (a : Dist n) → drift a (neg a) ≡ all-false n
sound-compl-meet-bot = compl-meet-bot

sound-compl-join-top : ∀ {n} (a : Dist n) → join a (neg a) ≡ all-true n
sound-compl-join-top = compl-join-top

sound-deMorgan₁ :
  ∀ {n} (a b : Dist n) → neg (drift a b) ≡ join (neg a) (neg b)
sound-deMorgan₁ = deMorgan₁

sound-deMorgan₂ :
  ∀ {n} (a b : Dist n) → neg (join a b) ≡ drift (neg a) (neg b)
sound-deMorgan₂ = deMorgan₂
