{-# OPTIONS --safe #-}

-- | Step 03: Vector Algebra Laws via Boolean Property Lifting
-- |
-- | Purpose:
-- |   Prove the remaining algebraic laws for distinction vectors
-- |   (beyond the basics in Step02_Soundness): idempotence, identities
-- |   (left/right), absorption, distributivity, De Morgan, complements.
-- |
-- | Method:
-- |   Structural induction on vectors; each head-step reduces to a
-- |   scalar Boolean law from Step01 (Soundness/Completeness), and the
-- |   tail-step uses the induction hypothesis.
-- |
-- | Dependency discipline:
-- |   - Uses ONLY our own Bool from Step01 (no Data.Bool).
-- |   - Imports Step01 Soundness+Completeness for scalar laws.
-- |   - Avoids re-proving theorems already present in Step02_Soundness
-- |     to prevent name clashes when opening modules publicly.

module Structures.S01_BooleanCore.Step03_AlgebraLaws where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Structures.S01_BooleanCore.Step01_BooleanFoundation
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Soundness
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Completeness
open import Structures.S01_BooleanCore.Step02_VectorOperations

------------------------------------------------------------------------
-- Helpful note:
-- Step02_Soundness already provides:
--   drift-assoc, drift-comm, drift-identityʳ, drift-zeroʳ,
--   join-assoc,  join-comm,  neg-involutive
-- We extend with: idempotence, identities (left), absorption,
-- distributivity (both ways), De Morgan (vector), complements.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- DRIFT (component-wise ∧): extra laws
------------------------------------------------------------------------

-- | Drift idempotence: drift a a ≡ a
drift-idempotent : ∀ {n} (a : Dist n) → drift a a ≡ a
drift-idempotent []       = refl
drift-idempotent (x ∷ xs) =
  cong₂ _∷_ (∧-idem x) (drift-idempotent xs)

-- | Left identity for drift: all-true is neutral on the left
drift-identityˡ : ∀ {n} (xs : Dist n) → drift (all-true n) xs ≡ xs
drift-identityˡ []       = refl
drift-identityˡ (x ∷ xs) =
  cong₂ _∷_ (∧-identityˡ x) (drift-identityˡ xs)

-- | Left zero for drift: all-false annihilates on the left
drift-zeroˡ : ∀ {n} (xs : Dist n) → drift (all-false n) xs ≡ all-false n
drift-zeroˡ []       = refl
drift-zeroˡ (x ∷ xs) =
  cong₂ _∷_ (∧-zeroˡ x) (drift-zeroˡ xs)

  -- | Absorption (vector level): drift xs (join xs ys) = xs
drift-absorb : ∀ {n} (xs ys : Dist n) → drift xs (join xs ys) ≡ xs
drift-absorb {zero} []       []       = refl
drift-absorb {suc n} (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (∧-absorb x y) (drift-absorb xs ys)

-- | Absorption (vector level): join xs (drift xs ys) = xs
join-absorb : ∀ {n} (xs ys : Dist n) → join xs (drift xs ys) ≡ xs
join-absorb {zero} []       []       = refl
join-absorb {suc n} (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (∨-absorb x y) (join-absorb xs ys)

------------------------------------------------------------------------
-- JOIN (component-wise ∨): extra laws
------------------------------------------------------------------------

-- | Join idempotence: join a a ≡ a
join-idempotent : ∀ {n} (a : Dist n) → join a a ≡ a
join-idempotent []       = refl
join-idempotent (x ∷ xs) =
  cong₂ _∷_ (∨-idem x) (join-idempotent xs)

-- | Right identity for join: all-false acts as neutral element
join-identityʳ : ∀ {n} (xs : Dist n) → join xs (all-false n) ≡ xs
join-identityʳ []       = refl
join-identityʳ (x ∷ xs) =
  cong₂ _∷_ (∨-identityʳ x) (join-identityʳ xs)

-- | Left identity for join
join-identityˡ : ∀ {n} (xs : Dist n) → join (all-false n) xs ≡ xs
join-identityˡ []       = refl
join-identityˡ (x ∷ xs) =
  cong₂ _∷_ (∨-identityˡ x) (join-identityˡ xs)

-- | “One” for join on the right: yields all-true
join-oneʳ : ∀ {n} (xs : Dist n) → join xs (all-true n) ≡ all-true n
join-oneʳ []       = refl
join-oneʳ (x ∷ xs) =
  cong₂ _∷_ (∨-oneʳ x) (join-oneʳ xs)

-- | “One” for join on the left
join-oneˡ : ∀ {n} (xs : Dist n) → join (all-true n) xs ≡ all-true n
join-oneˡ []       = refl
join-oneˡ (x ∷ xs) =
  cong₂ _∷_ (∨-oneˡ x) (join-oneˡ xs)

-- | Absorption for join: join xs (drift xs ys) ≡ xs
join-absorb : ∀ {n} (xs ys : Dist n) → join xs (drift xs ys) ≡ xs
join-absorb []       []       = refl
join-absorb (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (∨-absorb x y) (join-absorb xs ys)

------------------------------------------------------------------------
-- DISTRIBUTIVITY (both directions, lifted)
------------------------------------------------------------------------

-- | Right distributivity of drift over join:
--     drift (join a b) c ≡ join (drift a c) (drift b c)
drift-join-distrib-right : ∀ {n} (a b c : Dist n) →
  drift (join a b) c ≡ join (drift a c) (drift b c)
drift-join-distrib-right []       []       []       = refl
drift-join-distrib-right (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (∧-distrib-∨ x y z)
             (drift-join-distrib-right xs ys zs)

-- | Right distributivity of join over drift:
--     join a (drift b c) ≡ drift (join a b) (join a c)
join-drift-distrib-right : ∀ {n} (a b c : Dist n) →
  join a (drift b c) ≡ drift (join a b) (join a c)
join-drift-distrib-right []       []       []       = refl
join-drift-distrib-right (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (∨-distrib-∧ x y z)
             (join-drift-distrib-right xs ys zs)

------------------------------------------------------------------------
-- DE MORGAN (vector form) & COMPLEMENTS
------------------------------------------------------------------------

-- | De Morgan for vectors: ¬(xs ∧ ys) ≡ (¬xs) ∨ (¬ys)
demorgan-drift-join : ∀ {n} (xs ys : Dist n) →
  neg (drift xs ys) ≡ join (neg xs) (neg ys)
demorgan-drift-join []       []       = refl
demorgan-drift-join (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (DeMorgan-∧∨ x y) (demorgan-drift-join xs ys)

-- | De Morgan (dual): ¬(xs ∨ ys) ≡ (¬xs) ∧ (¬ys)
demorgan-join-drift : ∀ {n} (xs ys : Dist n) →
  neg (join xs ys) ≡ drift (neg xs) (neg ys)
demorgan-join-drift []       []       = refl
demorgan-join-drift (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (DeMorgan-∨∧ x y) (demorgan-join-drift xs ys)

-- | Complement vector laws
--   xs ∧ ¬xs ≡ all-false   and   xs ∨ ¬xs ≡ all-true
drift-complement : ∀ {n} (xs : Dist n) →
  drift xs (neg xs) ≡ all-false n
drift-complement []       = refl
drift-complement (x ∷ xs) =
  cong₂ _∷_ (∧-complement x) (drift-complement xs)

join-complement : ∀ {n} (xs : Dist n) →
  join xs (neg xs) ≡ all-true n
join-complement []       = refl
join-complement (x ∷ xs) =
  cong₂ _∷_ (∨-complement x) (join-complement xs)


------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
-- Added on top of Step02_Soundness:
--   • Drift:  idempotent, identityˡ, zeroˡ, absorption
--   • Join:   idempotent, identityˡ/ʳ, oneˡ/ʳ, absorption
--   • Distributivity:  ∧ over ∨  and  ∨ over ∧  (right-side forms)
--   • De Morgan (vector) and complement vector laws
-- All proofs are total (structural induction) and reduce to
-- scalar laws from Step01 (Soundness + Completeness).