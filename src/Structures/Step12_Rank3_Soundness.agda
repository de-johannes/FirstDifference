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

-- Reuse exactly what we need from Step 11 (public using, no empty renaming)
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
-- 0 · Auxiliary unfolding lemma for rank3? on 3+ lists
--     (matches the definition of rank3Witness / rank3?)
----------------------------------------------------------------------

rank3?-cons : ∀ (u v w : ℤ³) (rs : List ℤ³) →
  rank3? (u ∷ v ∷ w ∷ rs)
  ≡ (if nonZeroℤ (det3 u v w)
     then true
     else rank3? (v ∷ w ∷ rs))
rank3?-cons u v w rs = refl
-- Explanation: By definitions in Step 11:
--   rank3? xs = isJust (rank3Witness xs)
--   rank3Witness (u ∷ v ∷ w ∷ rs)
--     = if nonZeroℤ (det3 u v w)
--       then just …
--       else rank3Witness (v ∷ w ∷ rs)
--   isJust (just …) = true
--   isJust (…)      = rank3? (…)
-- hence the stated equality holds by computation (refl).

----------------------------------------------------------------------
-- 1 · Soundness: rank3? xs ≡ true  ⇒  HasGoodTriple xs
----------------------------------------------------------------------

soundness : ∀ xs → rank3? xs ≡ true → HasGoodTriple xs
-- Lists of length < 3: rank3? reduces to false, so the equality is impossible.
soundness []          ()
soundness (_ ∷ [])    ()
soundness (_ ∷ _ ∷ []) ()

-- Main case: xs = u ∷ v ∷ w ∷ rs
soundness (u ∷ v ∷ w ∷ rs) pr
  with nonZeroℤ (det3 u v w)
... | true  =
      -- In this branch, rank3? (u ∷ v ∷ w ∷ rs) reduces to true,
      -- thus we can produce 'here refl' as the witness.
      here {u = u} {v = v} {w = w} {rs = rs} refl
... | false =
      -- Rewrite 'pr' using rank3?-cons to obtain a proof on the tail:
      --   rank3? (u ∷ v ∷ w ∷ rs) ≡ true
      --   ≡⟨ sym (rank3?-cons u v w rs) ⟩
      --   (if false then true else rank3? (v ∷ w ∷ rs)) ≡ true
      --   ⇝ rank3? (v ∷ w ∷ rs) ≡ true
      let pr-tail : rank3? (v ∷ w ∷ rs) ≡ true
          pr-tail = trans (sym (rank3?-cons u v w rs)) pr
      in  there (soundness (v ∷ w ∷ rs) pr-tail)

----------------------------------------------------------------------
-- 2 · Soundness specialized to histories
----------------------------------------------------------------------

soundnessOnHistory :
  ∀ {n} (hist : List (Dist n)) →
  rank3OnHistoryBool hist ≡ true →
  HasGoodTriple (diffs (FoldMap³ {n} hist))
soundnessOnHistory {n} hist pr =
  soundness (diffs (FoldMap³ {n} hist)) pr

----------------------------------------------------------------------
-- 3 · Convenience re-exports (pair the two directions)
----------------------------------------------------------------------

-- completeness is provided by Step 11:
--   completeness : ∀ xs → HasGoodTriple xs → rank3? xs ≡ true

completeness' : ∀ xs → HasGoodTriple xs → rank3? xs ≡ true
completeness' = completeness

soundness' : ∀ xs → rank3? xs ≡ true → HasGoodTriple xs
soundness' = soundness

-- On histories:

completenessOnHistory' :
  ∀ {n} (hist : List (Dist n)) →
  HasGoodTriple (diffs (FoldMap³ {n} hist)) →
  rank3OnHistoryBool hist ≡ true
completenessOnHistory' = completenessOnHistory

soundnessOnHistory' :
  ∀ {n} (hist : List (Dist n)) →
  rank3OnHistoryBool hist ≡ true →
  HasGoodTriple (diffs (FoldMap³ {n} hist))
soundnessOnHistory' = soundnessOnHistory
