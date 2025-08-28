{-# OPTIONS --safe #-}

-- | Step 01: Boolean Foundation – Soundness Verification
-- |
-- | Purpose:
-- |   Collect and re-export all Boolean properties from Step01_BooleanFoundation
-- |   as a verified "soundness layer".
-- |
-- | Method:
-- |   Import the construction module, re-state each theorem, 
-- |   and prove soundness explicitly (here trivial by refl).
--
module Structures.01_BooleanCore.Step01_BooleanFoundation_Soundness where

open import Structures.01_BooleanCore.Step01_BooleanFoundation
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- | Soundness certificate: conjunction associativity
sound-∧-assoc : ∀ x y z → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
sound-∧-assoc = ∧-assoc

-- | Soundness certificate: conjunction commutativity
sound-∧-comm : ∀ x y → x ∧ y ≡ y ∧ x
sound-∧-comm = ∧-comm

-- | Soundness certificate: conjunction right identity
sound-∧-identityʳ : ∀ x → x ∧ true ≡ x
sound-∧-identityʳ = ∧-identityʳ

-- | Soundness certificate: conjunction idempotence
sound-∧-idem : ∀ x → x ∧ x ≡ x
sound-∧-idem = ∧-idem

-- | Soundness certificate: conjunction zero
sound-∧-zeroʳ : ∀ x → x ∧ false ≡ false
sound-∧-zeroʳ = ∧-zeroʳ

-- | Soundness certificate: disjunction commutativity
sound-∨-comm : ∀ x y → x ∨ y ≡ y ∨ x
sound-∨-comm = ∨-comm
