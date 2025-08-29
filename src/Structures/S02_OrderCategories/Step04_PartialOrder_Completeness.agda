{-# OPTIONS --safe #-}

-- | Step 04: Drift-Induced Partial Order — Completeness (finite)
-- |
-- | Purpose:
-- |   Show that for any finite family of distinction vectors, the
-- |   (finite) infimum/supremum exist. We implement them as folds:
-- |     bigMeet xs  = foldr drift   (all-true n)  xs
-- |     bigJoin xs  = foldr join    (all-false n) xs
-- |
-- | Method:
-- |   Structural induction on lists. The GLB/LUB properties follow
-- |   from Step04’s binary GLB/LUB lemmas combined with transitivity.
-- |
-- | Notes:
-- |   This proves "complete lattice" *for finite families*. For truly
-- |   arbitrary (possibly infinite) families you would need different
-- |   machinery (sets/indexed families), which is out of scope here.

module Structures.S02_OrderCategories.Step04_PartialOrder_Completeness where

open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)

-- Our Booleans and vector operations
open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool)
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; all-true; all-false)

-- Step 04 core order and lattice facts
open import Structures.S02_OrderCategories.Step04_PartialOrder
  using (_≤ᵈ_; ≤ᵈ-trans
       ; meet≤₁; meet≤₂; glb-≤ᵈ
       ; ub-join₁; ub-join₂; lub-≤ᵈ
       ; ⊥ᵈ; ⊥ᵈ-least; ⊤ᵈ; ⊤ᵈ-greatest
       )

------------------------------------------------------------------------
-- Finite "forall" over lists specialized to Dist n
------------------------------------------------------------------------

Forallᵈ : ∀ {n} → (Dist n → Set) → List (Dist n) → Set
Forallᵈ {n} P []       = ⊤
Forallᵈ {n} P (x ∷ xs) = P x × Forallᵈ P xs

------------------------------------------------------------------------
-- Finite infimum (meet) and supremum (join) via folds
------------------------------------------------------------------------

bigMeet : ∀ {n} → List (Dist n) → Dist n
bigMeet {n} []       = all-true n
bigMeet {n} (a ∷ as) = drift a (bigMeet as)

bigJoin : ∀ {n} → List (Dist n) → Dist n
bigJoin {n} []       = all-false n
bigJoin {n} (a ∷ as) = join a (bigJoin as)

------------------------------------------------------------------------
-- bigMeet: lower-bound and greatest-lower-bound properties
------------------------------------------------------------------------

-- Every element bounds bigMeet from above:  bigMeet xs ≤ᵈ a  for all a ∈ xs
bigMeet-lower : ∀ {n} (xs : List (Dist n)) → Forallᵈ (λ a → bigMeet xs ≤ᵈ a) xs
bigMeet-lower {n} []       = tt
bigMeet-lower {n} (a ∷ as) =
  let
    ih : Forallᵈ (λ b → bigMeet as ≤ᵈ b) as
    ih = bigMeet-lower as

    -- Promote each "bigMeet as ≤ᵈ b" to "drift a (bigMeet as) ≤ᵈ b"
    promote : Forallᵈ (λ b → bigMeet as ≤ᵈ b) as
            → Forallᵈ (λ b → drift a (bigMeet as) ≤ᵈ b) as
    promote []            = tt
    promote (p , ps)      = (≤ᵈ-trans (meet≤₂ a (bigMeet as)) p) , promote ps
  in
    ( meet≤₁ a (bigMeet as)    -- head: drift a (bigMeet as) ≤ᵈ a
    , promote ih               -- tail:  drift a (bigMeet as) ≤ᵈ each b in as
    )

-- Greatest-lower-bound: if c ≤ᵈ a for all a ∈ xs, then c ≤ᵈ bigMeet xs
bigMeet-greatest :
  ∀ {n} (xs : List (Dist n)) {c : Dist n}
  → Forallᵈ (λ a → c ≤ᵈ a) xs
  → c ≤ᵈ bigMeet xs
bigMeet-greatest {n} []       {c} _        = ⊤ᵈ-greatest c
bigMeet-greatest {n} (a ∷ as) {c} (p , ps) =
  glb-≤ᵈ p (bigMeet-greatest as ps)

------------------------------------------------------------------------
-- bigJoin: upper-bound and least-upper-bound properties
------------------------------------------------------------------------

-- Every element is below bigJoin:  a ≤ᵈ bigJoin xs  for all a ∈ xs
bigJoin-upper : ∀ {n} (xs : List (Dist n)) → Forallᵈ (λ a → a ≤ᵈ bigJoin xs) xs
bigJoin-upper {n} []       = tt
bigJoin-upper {n} (a ∷ as) =
  let
    ih : Forallᵈ (λ b → b ≤ᵈ bigJoin as) as
    ih = bigJoin-upper as

    -- Promote each "b ≤ᵈ bigJoin as" to "b ≤ᵈ join a (bigJoin as)"
    promote : Forallᵈ (λ b → b ≤ᵈ bigJoin as) as
            → Forallᵈ (λ b → b ≤ᵈ join a (bigJoin as)) as
    promote []            = tt
    promote (p , ps)      =
      let step : bigJoin as ≤ᵈ join a (bigJoin as)
          step = ub-join₂ a (bigJoin as)
      in (≤ᵈ-trans p step) , promote ps
  in
    ( ub-join₁ a (bigJoin as)  -- head: a ≤ᵈ join a (bigJoin as)
    , promote ih               -- tail:  b ≤ᵈ join a (bigJoin as) for each b in as
    )

-- Least-upper-bound: if a ≤ᵈ c for all a ∈ xs, then bigJoin xs ≤ᵈ c
bigJoin-least :
  ∀ {n} (xs : List (Dist n)) {c : Dist n}
  → Forallᵈ (λ a → a ≤ᵈ c) xs
  → bigJoin xs ≤ᵈ c
bigJoin-least {n} []       {c} _        = ⊥ᵈ-least c
bigJoin-least {n} (a ∷ as) {c} (p , ps) =
  let ih : bigJoin as ≤ᵈ c
      ih = bigJoin-least as ps
  in lub-≤ᵈ p ih

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
-- Provided:
--   • bigMeet xs  as finite GLB with  (bigMeet-lower, bigMeet-greatest)
--   • bigJoin xs  as finite LUB with  (bigJoin-upper, bigJoin-least)
-- This establishes Step 04 completeness for finite families (lists).
