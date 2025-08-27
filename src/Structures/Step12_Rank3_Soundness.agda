{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness (Bool ⇒ Spec) and History corollaries
--            Uses the Step 11 checker and spec; no postulates.
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List      using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

-- Dist is not re-exported by Step 11, import from Step 2:
open import Structures.Step2_VectorOperations using (Dist)

-- Reuse exactly what we need from Step 11
open import Structures.Step11_Rank3 public using
  ( ℤ³
  ; det3
  ; nonZeroℤ
  ; diffs
  ; FoldMap³
  ; HasGoodTriple
  ; here
  ; there
  ; rank3?
  ; rank3OnHistoryBool
  ; completeness
  )

----------------------------------------------------------------------
-- 0 · Inspect utility (to capture an equality from a decision)
----------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} → (x : A) → Inspect x
inspect x = it x refl

----------------------------------------------------------------------
-- 1 · Tiny β-lemma for 'if'
----------------------------------------------------------------------

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- 2 · Unfolding lemma for rank3? on lists with ≥ 3 elements
--     Matches the definition of rank3Witness / rank3? in Step 11.
----------------------------------------------------------------------

rank3?-cons : ∀ (u v w : ℤ³) (rs : List ℤ³) →
  rank3? (u ∷ v ∷ w ∷ rs)
  ≡ (if nonZeroℤ (det3 u v w)
     then true
     else rank3? (v ∷ w ∷ rs))
rank3?-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

----------------------------------------------------------------------
-- 3 · Soundness: rank3? xs ≡ true  ⇒  HasGoodTriple xs
----------------------------------------------------------------------

soundness : ∀ xs → rank3? xs ≡ true → HasGoodTriple xs
-- Lists of length < 3: impossible, since rank3? reduces to false.
soundness []          ()
soundness (_ ∷ [])    ()
soundness (_ ∷ _ ∷ []) ()

-- Main case: xs = u ∷ v ∷ w ∷ rs
soundness (u ∷ v ∷ w ∷ rs) pr
  with nonZeroℤ (det3 u v w) | inspect (nonZeroℤ (det3 u v w))
... | true  | it .true  eqTrue =
      -- We have eqTrue : nonZeroℤ (det3 u v w) ≡ true
      here {u = u} {v = v} {w = w} {rs = rs} eqTrue
... | false | it .false eqFalse =
      -- Transform 'pr' to a tail-proof using only propositional steps.
      there (soundness (v ∷ w ∷ rs) pr-tail)
  where
    -- Step 1: unfold rank3? to its conditional form
    pr-cond :
      (if nonZeroℤ (det3 u v w) then true else rank3? (v ∷ w ∷ rs)) ≡ true
    pr-cond = trans (sym (rank3?-cons u v w rs)) pr

    -- Step 2: substitute 'nonZeroℤ (det3 u v w) ≡ false'
    pr-false :
      (if false then true else rank3? (v ∷ w ∷ rs)) ≡ true
    pr-false =
      subst (λ b → (if b then true else rank3? (v ∷ w ∷ rs)) ≡ true)
            eqFalse
            pr-cond

    -- Step 3: β-reduce to the else-branch and obtain the tail proof
    pr-tail : rank3? (v ∷ w ∷ rs) ≡ true
    pr-tail = trans (sym (if-false-β true (rank3? (v ∷ w ∷ rs)))) pr-false

----------------------------------------------------------------------
-- 4 · Soundness specialized to histories
----------------------------------------------------------------------

soundnessOnHistory :
  ∀ {n} (hist : List (Dist n)) →
  rank3OnHistoryBool hist ≡ true →
  HasGoodTriple (diffs (FoldMap³ {n} hist))
soundnessOnHistory {n} hist pr =
  soundness (diffs (FoldMap³ {n} hist)) pr

----------------------------------------------------------------------
-- 5 · Convenience re-exports (pair the two directions)
----------------------------------------------------------------------

-- completeness is provided by Step 11:
--   completeness : ∀ xs → HasGoodTriple xs → rank3? xs ≡ true

completeness' : ∀ xs → HasGoodTriple xs → rank3? xs ≡ true
completeness' = completeness

soundness' : ∀ xs → rank3? xs ≡ true → HasGoodTriple xs
soundness' = soundness

-- On histories: define the completeness corollary directly.
completenessOnHistory' :
  ∀ {n} (hist : List (Dist n)) →
  HasGoodTriple (diffs (FoldMap³ {n} hist)) →
  rank3OnHistoryBool hist ≡ true
completenessOnHistory' {n} hist pr =
  completeness (diffs (FoldMap³ {n} hist)) pr
