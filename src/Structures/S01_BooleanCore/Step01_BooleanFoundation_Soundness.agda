-- src/Structures/S01_BooleanCore/Step01_BooleanFoundation_Soundness.agda
{-# OPTIONS --safe #-}

-- | Step 01 Soundness: Boolean algebra laws from pure D₀-Bool
module Structures.S01_BooleanCore.Step01_BooleanFoundation_Soundness where

open import Structures.S01_BooleanCore.Step01_BooleanFoundation
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Associativity of ∧
∧-assoc : ∀ x y z → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
∧-assoc true  true  true  = refl
∧-assoc true  true  false = refl
∧-assoc true  false true  = refl
∧-assoc true  false false = refl
∧-assoc false true  true  = refl
∧-assoc false true  false = refl
∧-assoc false false true  = refl
∧-assoc false false false = refl

-- Commutativity of ∧
∧-comm : ∀ x y → x ∧ y ≡ y ∧ x
∧-comm true  true  = refl
∧-comm true  false = refl
∧-comm false true  = refl
∧-comm false false = refl

-- Right identity of ∧
∧-identityʳ : ∀ x → x ∧ true ≡ x
∧-identityʳ true  = refl
∧-identityʳ false = refl

-- Idempotence of ∧
∧-idem : ∀ x → x ∧ x ≡ x
∧-idem true  = refl
∧-idem false = refl

-- Zero element of ∧
∧-zeroʳ : ∀ x → x ∧ false ≡ false
∧-zeroʳ true  = refl
∧-zeroʳ false = refl

-- Commutativity of ∨
∨-comm : ∀ x y → x ∨ y ≡ y ∨ x
∨-comm true  true  = refl
∨-comm true  false = refl
∨-comm false true  = refl
∨-comm false false = refl
