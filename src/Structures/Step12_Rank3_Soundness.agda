{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness from the Step 11 witness (safe)
--  Goal proved here:
--     ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
--  Strategy:
--    • Separate computation (rank3Witness) and proof (this file).
--    • Pure structural recursion on the list (no length index).
--    • A tiny helper lemma propagates the tail obligation in the
--      “head test = false” branch.
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

-- If you later want results over Dist histories, keep this import handy.
open import Structures.Step2_VectorOperations using (Dist)

-- Import exactly what we need from Step 11.
open import Structures.Step11_Rank3 public using
  ( ℤ³
  ; det3
  ; nonZeroℤ

  ; Maybe
  ; just
  ; nothing
  ; isJust
  ; rank3Witness

  ; HasGoodTriple
  ; here
  ; there
  ; pack
  )

----------------------------------------------------------------------
-- Small β-lemma for 'if false then ... else ...'
----------------------------------------------------------------------

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- Behaviour of isJust ∘ rank3Witness on lists with ≥ 3 elements.
-- This mirrors the head unfolding from Step 11.
----------------------------------------------------------------------

isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
  ≡ (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

----------------------------------------------------------------------
-- From a failed head test we extract the tail obligation:
--   if head-test = false and whole = true  ⇒  tail = true
----------------------------------------------------------------------

tailFromFalse :
  ∀ {u v w rs} →
  nonZeroℤ (det3 u v w) ≡ false →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs)) ≡ true →
  isJust (rank3Witness (v ∷ w ∷ rs)) ≡ true
tailFromFalse {u} {v} {w} {rs} eqFalse pr =
  let
    -- Replace LHS by its head unfolding and transport equality:
    pr-cond :
      (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-cond = trans (sym (isJust-cons u v w rs)) pr

    -- Substitute 'false' for the condition:
    pr-false :
      (if false then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-false =
      subst (λ b → (if b then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true)
            eqFalse
            pr-cond
  in
    -- Eliminate the 'if false' and conclude the tail is true:
    trans (sym (if-false-β true (isJust (rank3Witness (v ∷ w ∷ rs))))) pr-false

----------------------------------------------------------------------
-- Main theorem: whenever the program finds a witness (isJust = true),
-- the logical predicate HasGoodTriple holds.
-- Pure structural recursion on the list:
----------------------------------------------------------------------

witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs

-- Length < 3: impossible, rank3Witness = nothing ⇒ isJust = false
witnessSound [] ()
witnessSound (_ ∷ []) ()
witnessSound (_ ∷ _ ∷ []) ()

-- Length ≥ 3: test the head triple; if true we are done, else recurse on the tail
witnessSound (u ∷ v ∷ w ∷ rs) pr with nonZeroℤ (det3 u v w)
... | true  = here refl
... | false = there (witnessSound (v ∷ w ∷ rs) (tailFromFalse refl pr))
