{-# OPTIONS --safe #-}

-- | Step 05: Join-Semilattice on Dist
-- |
-- | Ziel:
-- |   (Dist n, _≤ᵈ_, join) ist ein Join-Semilattice:
-- |   • join ist das kleinste obere Schranken-Element (LUB)
-- |   • daraus folgen Idempotenz, Kommutativität, Assoziativität
-- |
-- | Beweise stützen sich NUR auf Step04 (Ordnung & UB/LUB).

module Structures.S02_OrderCategories.Step05_JoinSemilattice where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Structures.S01_BooleanCore.Step02_VectorOperations using (Dist; join)
open import Structures.S02_OrderCategories.Step04_PartialOrder
  using (_≤ᵈ_; ≤ᵈ-refl; ≤ᵈ-trans; ≤ᵈ-antisym
       ; ub-join₁ ; ub-join₂ ; lub-≤ᵈ)

------------------------------------------------------------------------
-- Upper Bound / Least Upper Bound
------------------------------------------------------------------------

record IsUpperBound {n : ℕ} (x y j : Dist n) : Set where
  constructor mkUB
  field
    leftUB  : x ≤ᵈ j
    rightUB : y ≤ᵈ j

record IsJoin {n : ℕ} (x y j : Dist n) : Set where
  constructor mkJoin
  field
    isUB  : IsUpperBound x y j
    least : ∀ {r} → IsUpperBound x y r → j ≤ᵈ r

open IsUpperBound public
open IsJoin public

------------------------------------------------------------------------
-- Proof: join is the LUB
------------------------------------------------------------------------

join-isUB : ∀ {n} (x y : Dist n) → IsUpperBound x y (join x y)
join-isUB x y = mkUB (ub-join₁ x y) (ub-join₂ x y)

join-least : ∀ {n} (x y j : Dist n) →
             IsUpperBound x y j → join x y ≤ᵈ j
join-least x y j (mkUB x≤j y≤j) = lub-≤ᵈ x≤j y≤j

join-isJoin : ∀ {n} (x y : Dist n) → IsJoin x y (join x y)
join-isJoin x y =
  mkJoin (join-isUB x y)
         (λ {r} ub → join-least x y r ub)   -- <<< eta-Anpassung

------------------------------------------------------------------------
-- Algebraic laws derived from the LUB property
------------------------------------------------------------------------

-- Idempotence:  join x x ≡ x
join-idem : ∀ {n} (x : Dist n) → join x x ≡ x
join-idem x =
  let left  : join x x ≤ᵈ x
      left  = lub-≤ᵈ (≤ᵈ-refl x) (≤ᵈ-refl x)
      right : x ≤ᵈ join x x
      right = ub-join₁ x x
  in ≤ᵈ-antisym left right

-- Commutativity:  join x y ≡ join y x
join-comm : ∀ {n} (x y : Dist n) → join x y ≡ join y x
join-comm x y =
  let a : join x y ≤ᵈ join y x
      a = lub-≤ᵈ (ub-join₂ y x) (ub-join₁ y x)
      b : join y x ≤ᵈ join x y
      b = lub-≤ᵈ (ub-join₂ x y) (ub-join₁ x y)
  in ≤ᵈ-antisym a b

-- Associativity:  join (join x y) z ≡ join x (join y z)
join-assoc : ∀ {n} (x y z : Dist n) →
             join (join x y) z ≡ join x (join y z)
join-assoc x y z =
  let
    -- Richtung 1: (x∨y)∨z ≤ x∨(y∨z)
    xy≤x_yz : join x y ≤ᵈ join x (join y z)
    xy≤x_yz =
      let x≤ : x ≤ᵈ join x (join y z)
          x≤ = ub-join₁ x (join y z)
          y≤ : y ≤ᵈ join x (join y z)
          y≤ = ≤ᵈ-trans (ub-join₁ y z) (ub-join₂ x (join y z))
      in lub-≤ᵈ x≤ y≤

    z≤x_yz : z ≤ᵈ join x (join y z)
    z≤x_yz = ≤ᵈ-trans (ub-join₂ y z) (ub-join₂ x (join y z))

    L : join (join x y) z ≤ᵈ join x (join y z)
    L = lub-≤ᵈ xy≤x_yz z≤x_yz

    -- Richtung 2: x∨(y∨z) ≤ (x∨y)∨z
    x≤xy_z : x ≤ᵈ join (join x y) z
    x≤xy_z = ≤ᵈ-trans (ub-join₁ x y) (ub-join₁ (join x y) z)

    yz≤xy_z : join y z ≤ᵈ join (join x y) z
    yz≤xy_z =
      let y≤ : y ≤ᵈ join (join x y) z
          y≤ = ≤ᵈ-trans (ub-join₂ x y) (ub-join₁ (join x y) z)
          z≤ : z ≤ᵈ join (join x y) z
          z≤ = ub-join₂ (join x y) z
      in lub-≤ᵈ y≤ z≤

    R : join x (join y z) ≤ᵈ join (join x y) z
    R = lub-≤ᵈ x≤xy_z yz≤xy_z
  in ≤ᵈ-antisym L R
