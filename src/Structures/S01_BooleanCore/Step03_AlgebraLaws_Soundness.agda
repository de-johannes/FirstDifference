-- src/Structures/S01_BooleanCore/Step03_Soundness.agda
{-# OPTIONS --safe #-}

-- | Step 03: Vector Algebra — Soundness Wrapper
-- |
-- | Purpose:
-- |   Re-export the completeness-level vector laws proven in
-- |   Step03_AlgebraLaws as soundness certificates with stable names.
-- |
-- | Method:
-- |   Simple aliasing of theorems (no new proofs). Keeps the pattern
-- |   consistent with Step01/02 and makes All.agda imports ergonomic.

module Structures.S01_BooleanCore.Step03_Soundness where

open import Structures.S01_BooleanCore.Step01_BooleanFoundation                -- Bool + ops
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Soundness      -- scalar ∧/∨ laws
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Completeness   -- scalar completeness
open import Structures.S01_BooleanCore.Step02_VectorOperations                  -- Dist, drift, join, neg
open import Structures.S01_BooleanCore.Step03_AlgebraLaws

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

-- Drift (∧) — extras
sound-drift-idempotent : ∀ {n} (a : Dist n) → drift a a ≡ a
sound-drift-idempotent = drift-idempotent

sound-drift-identityˡ : ∀ {n} (xs : Dist n) → drift (all-true n) xs ≡ xs
sound-drift-identityˡ = drift-identityˡ

sound-drift-zeroˡ : ∀ {n} (xs : Dist n) → drift (all-false n) xs ≡ all-false n
sound-drift-zeroˡ = drift-zeroˡ

sound-drift-absorb : ∀ {n} (xs ys : Dist n) → drift xs (join xs ys) ≡ xs
sound-drift-absorb = drift-absorb

-- Join (∨) — extras
sound-join-idempotent : ∀ {n} (a : Dist n) → join a a ≡ a
sound-join-idempotent = join-idempotent

sound-join-identityʳ : ∀ {n} (xs : Dist n) → join xs (all-false n) ≡ xs
sound-join-identityʳ = join-identityʳ

sound-join-identityˡ : ∀ {n} (xs : Dist n) → join (all-false n) xs ≡ xs
sound-join-identityˡ = join-identityˡ

sound-join-oneʳ : ∀ {n} (xs : Dist n) → join xs (all-true n) ≡ all-true n
sound-join-oneʳ = join-oneʳ

sound-join-oneˡ : ∀ {n} (xs : Dist n) → join (all-true n) xs ≡ all-true n
sound-join-oneˡ = join-oneˡ

sound-join-absorb : ∀ {n} (xs ys : Dist n) → join xs (drift xs ys) ≡ xs
sound-join-absorb = join-absorb

-- Distributivität (beide Richtungen)
sound-drift-join-distrib-right : ∀ {n} (a b c : Dist n) →
  drift (join a b) c ≡ join (drift a c) (drift b c)
sound-drift-join-distrib-right = drift-join-distrib-right

sound-join-drift-distrib-right : ∀ {n} (a b c : Dist n) →
  join a (drift b c) ≡ drift (join a b) (join a c)
sound-join-drift-distrib-right = join-drift-distrib-right

-- De Morgan (vektoriell) & Komplemente
sound-demorgan-drift-join : ∀ {n} (xs ys : Dist n) →
  neg (drift xs ys) ≡ join (neg xs) (neg ys)
sound-demorgan-drift-join = demorgan-drift-join

sound-demorgan-join-drift : ∀ {n} (xs ys : Dist n) →
  neg (join xs ys) ≡ drift (neg xs) (neg ys)
sound-demorgan-join-drift = demorgan-join-drift

sound-drift-complement : ∀ {n} (xs : Dist n) →
  drift xs (neg xs) ≡ all-false n
sound-drift-complement = drift-complement

sound-join-complement : ∀ {n} (xs : Dist n) →
  join xs (neg xs) ≡ all-true n
sound-join-complement = join-complement