{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness (Bool ⇒ Spec) and History corollaries
--            Uses the Step 11 checker and spec; no postulates.
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List      using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

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
-- 1 · Unfolding lemma for rank3? on lists with ≥ 3 elements
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
-- Explanation:
--   rank3? (u ∷ v ∷ w ∷ rs)
--   = if nonZeroℤ (det3 u v w) then true else rank3? (v ∷ w ∷ rs)

----------------------------------------------------------------------
-- 2 · Soundness: rank3? xs ≡ true  ⇒  HasGoodTriple xs
----------------------------------------------------------------------

soundness : ∀ xs → rank3? xs ≡ true → HasGoodTriple xs
-- Lists of length < 3: rank3? reduces to false, so the equality is impossible.
soundness []          ()
soundness (_ ∷ [])    ()
soundness (_ ∷ _ ∷ []) ()

-- Main case: xs = u ∷ v ∷ w ∷ rs
soundness (u ∷ v ∷ w ∷ rs) pr
  with inspect (nonZeroℤ (det3 u v w))
... | it true  eq =
      -- We have eq : nonZeroℤ (det3 u v w) ≡ true
      here {u = u} {v = v} {w = w} {rs = rs} eq
... | it false _  =
      -- Rewrite 'pr' using rank3?-cons to get a tail proof:
      let pr-tail : rank3? (v ∷ w ∷ rs) ≡ true
          pr-tail = trans (sym (rank3?-cons u v w rs)) pr
      in  there (soundness (v ∷ w ∷ rs) pr-tail)

----------------------------------------------------------------------
-- 3 · Soundness specialized to histories
----------------------------------------------------------------------

soundnessOnHistory :
  ∀ {n} (hist : List (Dist n)) →
  rank3OnHistoryBool hist ≡ true →
  HasGoodTriple (diffs (FoldMap³ {n} hist))
soundnessOnHistory {n} hist pr =
  soundness (diffs (FoldMap³ {n} hist)) pr

----------------------------------------------------------------------
-- 4 · Convenience re-exports (pair the two directions)
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
