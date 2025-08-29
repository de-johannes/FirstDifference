{-# OPTIONS --safe #-}

-- | Step 03: Vector Algebra Laws — Soundness Layer
-- |
-- | Purpose:
-- |   Provide explicit "soundness certificates" for all vector-level
-- |   Boolean laws proven in Step03_AlgebraLaws. Using distinct names
-- |   (sound-…) avoids clashes when opening both modules publicly.
-- |
-- | Method:
-- |   Certificates are either direct renamings of Step02 soundness results
-- |   (for assoc/comm) or direct aliases to theorems from Step03_AlgebraLaws.
-- |   No new proofs are introduced here.
-- |
-- | Guarantee:
-- |   Fully machine-checked under --safe; zero postulates/axioms.

module Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_)

-- Dist-level operations and constants
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; neg; all-true; all-false)

-- Bring in assoc/comm from Step02 soundness, but expose them under sound-* names.
-- This avoids accidental picking of vector-level variants and keeps Step05 clean.
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  renaming ( drift-assoc to sound-drift-assoc
           ; drift-comm  to sound-drift-comm
           ; join-assoc  to sound-join-assoc
           ; join-comm   to sound-join-comm)

-- Remaining algebraic laws live in Step03_AlgebraLaws; we re-expose them as sound-*
open import Structures.S01_BooleanCore.Step03_AlgebraLaws

------------------------------------------------------------------------
-- DRIFT (component-wise ∧)
------------------------------------------------------------------------

-- Idempotence, identity, zero, absorption
sound-drift-idempotent :
  ∀ {n} (a : Dist n) → drift a a ≡ a
sound-drift-idempotent = drift-idempotent

sound-drift-identityˡ :
  ∀ {n} (xs : Dist n) → drift (all-true n) xs ≡ xs
sound-drift-identityˡ = drift-identityˡ

sound-drift-zeroˡ :
  ∀ {n} (xs : Dist n) → drift (all-false n) xs ≡ all-false n
sound-drift-zeroˡ = drift-zeroˡ

sound-drift-absorb :
  ∀ {n} (xs ys : Dist n) → drift xs (join xs ys) ≡ xs
sound-drift-absorb = drift-absorb

------------------------------------------------------------------------
-- JOIN (component-wise ∨)
------------------------------------------------------------------------

-- Idempotence, identities, ones, absorption
sound-join-idempotent :
  ∀ {n} (a : Dist n) → join a a ≡ a
sound-join-idempotent = join-idempotent

sound-join-identityʳ :
  ∀ {n} (xs : Dist n) → join xs (all-false n) ≡ xs
sound-join-identityʳ = join-identityʳ

sound-join-identityˡ :
  ∀ {n} (xs : Dist n) → join (all-false n) xs ≡ xs
sound-join-identityˡ = join-identityˡ

sound-join-oneʳ :
  ∀ {n} (xs : Dist n) → join xs (all-true n) ≡ all-true n
sound-join-oneʳ = join-oneʳ

sound-join-oneˡ :
  ∀ {n} (xs : Dist n) → join (all-true n) xs ≡ all-true n
sound-join-oneˡ = join-oneˡ

sound-join-absorb :
  ∀ {n} (xs ys : Dist n) → join xs (drift xs ys) ≡ xs
sound-join-absorb = join-absorb

------------------------------------------------------------------------
-- DISTRIBUTIVITY (lifted)
------------------------------------------------------------------------

sound-drift-join-distrib-right :
  ∀ {n} (a b c : Dist n) →
  drift (join a b) c ≡ join (drift a c) (drift b c)
sound-drift-join-distrib-right = drift-join-distrib-right

sound-join-drift-distrib-right :
  ∀ {n} (a b c : Dist n) →
  join a (drift b c) ≡ drift (join a b) (join a c)
sound-join-drift-distrib-right = join-drift-distrib-right

------------------------------------------------------------------------
-- DE MORGAN & COMPLEMENTS (lifted)
------------------------------------------------------------------------

sound-demorgan-drift-join :
  ∀ {n} (xs ys : Dist n) →
  neg (drift xs ys) ≡ join (neg xs) (neg ys)
sound-demorgan-drift-join = demorgan-drift-join

sound-demorgan-join-drift :
  ∀ {n} (xs ys : Dist n) →
  neg (join xs ys) ≡ drift (neg xs) (neg ys)
sound-demorgan-join-drift = demorgan-join-drift

sound-drift-complement :
  ∀ {n} (xs : Dist n) →
  drift xs (neg xs) ≡ all-false n
sound-drift-complement = drift-complement

sound-join-complement :
  ∀ {n} (xs : Dist n) →
  join xs (neg xs) ≡ all-true n
sound-join-complement = join-complement

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
-- This module provides stable, uniquely named certificates for the vector
-- algebra laws at Dist level. Assoc/comm are imported from Step02 soundness
-- under sound-* names; all other laws are aliased from Step03_AlgebraLaws.