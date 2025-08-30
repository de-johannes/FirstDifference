{-# OPTIONS --safe #-}

-- | Step 03: Vector Algebra Laws via Boolean Property Lifting
-- |
-- | Purpose:
-- |   Lift all remaining Boolean algebra laws (from Step01 Soundness
-- |   + Completeness) to n-dimensional distinction vectors (Dist n).
-- |
-- | Method:
-- |   Structural induction on vectors. Each case reduces to the
-- |   corresponding scalar law on Bool, and the tail is handled by
-- |   induction hypothesis.
-- |
-- | Guarantee:
-- |   Every property is fully verified under Agda’s --safe flag.
-- |   No postulates, no external axioms.
-- |
-- | Interpretation:
-- |   This establishes that Dist n (Boolean vectors) form a complete
-- |   Boolean algebra in every dimension.

module Structures.S01_BooleanCore.Step03_AlgebraLaws where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Structures.S01_BooleanCore.Step01_BooleanFoundation
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Soundness
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Completeness
open import Structures.S01_BooleanCore.Step02_VectorOperations

------------------------------------------------------------------------
-- DRIFT (component-wise ∧)
------------------------------------------------------------------------

drift-idempotent : ∀ {n} (a : Dist n) → drift a a ≡ a
drift-idempotent []       = refl
drift-idempotent (x ∷ xs) =
  cong₂ _∷_ (∧-idem x) (drift-idempotent xs)

drift-identityˡ : ∀ {n} (xs : Dist n) → drift (all-true n) xs ≡ xs
drift-identityˡ []       = refl
drift-identityˡ (x ∷ xs) =
  cong₂ _∷_ (∧-identityˡ x) (drift-identityˡ xs)

drift-zeroˡ : ∀ {n} (xs : Dist n) → drift (all-false n) xs ≡ all-false n
drift-zeroˡ []       = refl
drift-zeroˡ (x ∷ xs) =
  cong₂ _∷_ (∧-zeroˡ x) (drift-zeroˡ xs)

drift-absorb : ∀ {n} (xs ys : Dist n) → drift xs (join xs ys) ≡ xs
drift-absorb []       []       = refl
drift-absorb (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (∧-absorb x y) (drift-absorb xs ys)

------------------------------------------------------------------------
-- JOIN (component-wise ∨)
------------------------------------------------------------------------

join-idempotent : ∀ {n} (a : Dist n) → join a a ≡ a
join-idempotent []       = refl
join-idempotent (x ∷ xs) =
  cong₂ _∷_ (∨-idem x) (join-idempotent xs)

join-identityʳ : ∀ {n} (xs : Dist n) → join xs (all-false n) ≡ xs
join-identityʳ []       = refl
join-identityʳ (x ∷ xs) =
  cong₂ _∷_ (∨-identityʳ x) (join-identityʳ xs)

join-identityˡ : ∀ {n} (xs : Dist n) → join (all-false n) xs ≡ xs
join-identityˡ []       = refl
join-identityˡ (x ∷ xs) =
  cong₂ _∷_ (∨-identityˡ x) (join-identityˡ xs)

join-oneʳ : ∀ {n} (xs : Dist n) → join xs (all-true n) ≡ all-true n
join-oneʳ []       = refl
join-oneʳ (x ∷ xs) =
  cong₂ _∷_ (∨-oneʳ x) (join-oneʳ xs)

join-oneˡ : ∀ {n} (xs : Dist n) → join (all-true n) xs ≡ all-true n
join-oneˡ []       = refl
join-oneˡ (x ∷ xs) =
  cong₂ _∷_ (∨-oneˡ x) (join-oneˡ xs)

join-absorb : ∀ {n} (xs ys : Dist n) → join xs (drift xs ys) ≡ xs
join-absorb []       []       = refl
join-absorb (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (∨-absorb x y) (join-absorb xs ys)

------------------------------------------------------------------------
-- DISTRIBUTIVITY (lifted)
------------------------------------------------------------------------

drift-join-distrib-right :
  ∀ {n} (a b c : Dist n) →
  drift (join a b) c ≡ join (drift a c) (drift b c)
drift-join-distrib-right []       []       []       = refl
drift-join-distrib-right (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (∧-distrib-∨ x y z)
             (drift-join-distrib-right xs ys zs)

join-drift-distrib-right :
  ∀ {n} (a b c : Dist n) →
  join a (drift b c) ≡ drift (join a b) (join a c)
join-drift-distrib-right []       []       []       = refl
join-drift-distrib-right (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (∨-distrib-∧ x y z)
             (join-drift-distrib-right xs ys zs)

------------------------------------------------------------------------
-- DE MORGAN & COMPLEMENTS (lifted)
------------------------------------------------------------------------

demorgan-drift-join :
  ∀ {n} (xs ys : Dist n) →
  neg (drift xs ys) ≡ join (neg xs) (neg ys)
demorgan-drift-join []       []       = refl
demorgan-drift-join (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (DeMorgan-∧∨ x y) (demorgan-drift-join xs ys)

demorgan-join-drift :
  ∀ {n} (xs ys : Dist n) →
  neg (join xs ys) ≡ drift (neg xs) (neg ys)
demorgan-join-drift []       []       = refl
demorgan-join-drift (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (DeMorgan-∨∧ x y) (demorgan-join-drift xs ys)

drift-complement :
  ∀ {n} (xs : Dist n) →
  drift xs (neg xs) ≡ all-false n
drift-complement []       = refl
drift-complement (x ∷ xs) =
  cong₂ _∷_ (∧-complement x) (drift-complement xs)

join-complement :
  ∀ {n} (xs : Dist n) →
  join xs (neg xs) ≡ all-true n
join-complement []       = refl
join-complement (x ∷ xs) =
  cong₂ _∷_ (∨-complement x) (join-complement xs)

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
-- Added on top of Step02_Soundness:
--   • Drift:  idempotence, identityˡ, zeroˡ, absorption
--   • Join:   idempotence, identityˡ/ʳ, oneˡ/ʳ, absorption
--   • Distributivity both ways
--   • De Morgan (vector) and complement vector laws
-- This completes the Boolean algebra laws for Dist n.