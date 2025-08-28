{-# OPTIONS --safe #-}

-- | Step 01: Boolean Foundation — Completeness Layer
-- |
-- | Purpose:
-- |   Provide the full set of classical Boolean laws to make
-- |   the scalar algebra complete for downstream vector/category/time
-- |   developments.
-- |
-- | Method:
-- |   Exhaustive case analysis over {true,false}. All proofs are total,
-- |   under --safe, with no postulates.
-- |
-- | Relation to Soundness:
-- |   Complements Step01_Soundness by adding all additional laws
-- |   (identities, absorption, distributivity, complements, De Morgan, …).

module Structures.S01_BooleanCore.Step01_BooleanFoundation_Completeness where

open import Structures.S01_BooleanCore.Step01_BooleanFoundation
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Identities, Idempotence, Zeros, Ones
------------------------------------------------------------------------

∧-identityˡ : ∀ x → true ∧ x ≡ x
∧-identityˡ true  = refl
∧-identityˡ false = refl

∨-identityʳ : ∀ x → x ∨ false ≡ x
∨-identityʳ true  = refl
∨-identityʳ false = refl

∨-identityˡ : ∀ x → false ∨ x ≡ x
∨-identityˡ true  = refl
∨-identityˡ false = refl

∧-zeroˡ : ∀ x → false ∧ x ≡ false
∧-zeroˡ true  = refl
∧-zeroˡ false = refl

∨-oneʳ : ∀ x → x ∨ true ≡ true
∨-oneʳ true  = refl
∨-oneʳ false = refl

∨-oneˡ : ∀ x → true ∨ x ≡ true
∨-oneˡ true  = refl
∨-oneˡ false = refl

∨-idem : ∀ x → x ∨ x ≡ x
∨-idem true  = refl
∨-idem false = refl

------------------------------------------------------------------------
-- Absorption
------------------------------------------------------------------------

∧-absorb : ∀ x y → x ∧ (x ∨ y) ≡ x
∧-absorb true  y = refl
∧-absorb false y = refl

∨-absorb : ∀ x y → x ∨ (x ∧ y) ≡ x
∨-absorb true  y = refl
∨-absorb false y = refl

------------------------------------------------------------------------
-- Distributivity
------------------------------------------------------------------------

∧-distrib-∨ : ∀ (x y z : Bool) → (x ∨ y) ∧ z ≡ (x ∧ z) ∨ (y ∧ z)
∧-distrib-∨ true  true  true  = refl
∧-distrib-∨ true  true  false = refl
∧-distrib-∨ true  false true  = refl
∧-distrib-∨ true  false false = refl
∧-distrib-∨ false true  true  = refl
∧-distrib-∨ false true  false = refl
∧-distrib-∨ false false true  = refl
∧-distrib-∨ false false false = refl

∨-distrib-∧ : ∀ (x y z : Bool) → x ∨ (y ∧ z) ≡ (x ∨ y) ∧ (x ∨ z)
∨-distrib-∧ true  y z = refl
∨-distrib-∧ false y z = refl

------------------------------------------------------------------------
-- Complements & De Morgan
------------------------------------------------------------------------

not-involutive : ∀ x → not (not x) ≡ x
not-involutive true  = refl
not-involutive false = refl

∧-complement : ∀ x → x ∧ not x ≡ false
∧-complement true  = refl
∧-complement false = refl

∨-complement : ∀ x → x ∨ not x ≡ true
∨-complement true  = refl
∨-complement false = refl

DeMorgan-∧∨ : ∀ x y → not (x ∧ y) ≡ (not x) ∨ (not y)
DeMorgan-∧∨ true  true  = refl
DeMorgan-∧∨ true  false = refl
DeMorgan-∧∨ false true  = refl
DeMorgan-∧∨ false false = refl

DeMorgan-∨∧ : ∀ x y → not (x ∨ y) ≡ (not x) ∧ (not y)
DeMorgan-∨∧ true  true  = refl
DeMorgan-∨∧ true  false = refl
DeMorgan-∨∧ false true  = refl
DeMorgan-∨∧ false false = refl

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
-- Proven here in addition to Step01_Soundness:
--   • Identities (∧/∨, left/right), zeros & ones
--   • Idempotence for ∨
--   • Absorption
--   • Distributivity both ways
--   • Complements (x ∧ ¬x = ⊥,  x ∨ ¬x = ⊤)
--   • Double negation, De Morgan
--
-- Together: Soundness + Completeness = full Boolean algebra,
-- machine-checked and ready for vector/category lifting.