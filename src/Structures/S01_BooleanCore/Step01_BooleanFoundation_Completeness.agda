{-# OPTIONS --safe #-}

-- | Step 01: Boolean Foundation — Completeness Layer
-- |
-- | Purpose:
-- |   Provide the remaining classical Boolean laws to make the
-- |   scalar algebra practically complete for downstream use
-- |   (vectors, categories, time, …).
-- |
-- | Method:
-- |   Exhaustive case analysis over {true,false}. All proofs are total,
-- |   under --safe, with no postulates.
-- |
-- | Relation to Soundness:
-- |   Complements the Soundness module by adding the standard
-- |   laws typically expected from Boolean algebra (identities,
-- |   idempotence for ∨, absorption, distributivity, complements,
-- |   De Morgan, double negation).

module Structures.S01_BooleanCore.Step01_BooleanFoundation_Completeness where

open import Structures.S01_BooleanCore.Step01_BooleanFoundation
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Identities & Idempotence (dual side & missing cases)
------------------------------------------------------------------------

-- Left identity for ∧ (dual of right identity via commutativity)
∧-identityˡ : ∀ x → true ∧ x ≡ x
∧-identityˡ true  = refl
∧-identityˡ false = refl

-- Idempotence for ∨
∨-idem : ∀ x → x ∨ x ≡ x
∨-idem true  = refl
∨-idem false = refl

-- Right identity for ∨
∨-identityʳ : ∀ x → x ∨ false ≡ x
∨-identityʳ true  = refl
∨-identityʳ false = refl

-- “One”/absorbing element for ∨ (dual zum ∧-Zero)
∨-oneʳ : ∀ x → x ∨ true ≡ true
∨-oneʳ true  = refl
∨-oneʳ false = refl

-- Left identity for ∨ (aus Kommutativität ableitbar, hier explizit)
∨-identityˡ : ∀ x → false ∨ x ≡ x
∨-identityˡ true  = refl
∨-identityˡ false = refl

-- Left “one” for ∨
∨-oneˡ : ∀ x → true ∨ x ≡ true
∨-oneˡ true  = refl
∨-oneˡ false = refl

-- Left zero for ∧ (dual zum rechten)
∧-zeroˡ : ∀ x → false ∧ x ≡ false
∧-zeroˡ true  = refl
∧-zeroˡ false = refl

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

∧-distrib-∨ : ∀ x y z → x ∧ (y ∨ z) ≡ (x ∧ y) ∨ (x ∧ z)
∧-distrib-∨ true  y z = refl
∧-distrib-∨ false y z = refl

∨-distrib-∧ : ∀ x y z → x ∨ (y ∧ z) ≡ (x ∨ y) ∧ (x ∨ z)
∨-distrib-∧ true  y z = refl
∨-distrib-∧ false y z = refl

------------------------------------------------------------------------
-- Complements & De Morgan
------------------------------------------------------------------------

-- Double negation (global, wird auch in Step02 genutzt)
not-involutive : ∀ x → not (not x) ≡ x
not-involutive true  = refl
not-involutive false = refl

-- Complement laws
∧-complement : ∀ x → x ∧ not x ≡ false
∧-complement true  = refl
∧-complement false = refl

∨-complement : ∀ x → x ∨ not x ≡ true
∨-complement true  = refl
∨-complement false = refl

-- De Morgan laws
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
--   • Identities (left/right) and zeros for ∧ and ∨
--   • Idempotence for ∨
--   • Absorption:  x ∧ (x ∨ y) ≡ x,   x ∨ (x ∧ y) ≡ x
--   • Distributivity both ways
--   • Complements: x ∧ ¬x ≡ false,  x ∨ ¬x ≡ true
--   • De Morgan + double negation