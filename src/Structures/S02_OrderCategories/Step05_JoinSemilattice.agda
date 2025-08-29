{-# OPTIONS --safe #-}

-- | Step 05: Join-Semilattice on Dist
-- |
-- | Goal:
-- |   Show that (Dist n, ⊑, join) is a join-semilattice.
-- |   Proof uses:
-- |     • Algebra laws on Dist (Step03)
-- |     • Order structure (Step04)
-- |
-- | Result:
-- |   join is the least upper bound (LUB).
-- |   Laws: idempotence, commutativity, associativity.
-- |
-- | All machine-checked under --safe.

module Structures.S02_OrderCategories.Step05_JoinSemilattice where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Structures.S01_BooleanCore.Step02_VectorOperations using (Dist; join)
open import Structures.S01_BooleanCore.Step03_AlgebraLaws
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
open import Structures.S02_OrderCategories.Step04_PartialOrder

------------------------------------------------------------------------
-- Upper Bound / Least Upper Bound
------------------------------------------------------------------------

record IsUpperBound {n : ℕ} (x y j : Dist n) : Set where
  constructor mkUB
  field
    leftUB  : x ⊑ j
    rightUB : y ⊑ j

record IsJoin {n : ℕ} (x y j : Dist n) : Set where
  constructor mkJoin
  field
    isUB  : IsUpperBound x y j
    least : ∀ {r} → IsUpperBound x y r → j ⊑ r

open IsUpperBound public
open IsJoin public

------------------------------------------------------------------------
-- Proof: join is the LUB
------------------------------------------------------------------------

join-isUB : ∀ {n} (x y : Dist n) → IsUpperBound x y (join x y)
join-isUB x y = mkUB (join-upper₁ x y) (join-upper₂ x y)

join-least : ∀ {n} (x y j : Dist n) →
             IsUpperBound x y j → join x y ⊑ j
join-least x y j (mkUB x≤j y≤j) = join-lub x y j x≤j y≤j

join-isJoin : ∀ {n} (x y : Dist n) → IsJoin x y (join x y)
join-isJoin x y = mkJoin (join-isUB x y) (join-least x y)

------------------------------------------------------------------------
-- Algebraic laws (from Step03, lifted to Dist)
------------------------------------------------------------------------

join-idem : ∀ {n} (x : Dist n) → join x x ≡ x
join-idem = sound-join-idem

join-comm : ∀ {n} (x y : Dist n) → join x y ≡ join y x
join-comm = sound-join-comm

join-assoc : ∀ {n} (x y z : Dist n) →
             join (join x y) z ≡ join x (join y z)
join-assoc = sound-join-assoc
