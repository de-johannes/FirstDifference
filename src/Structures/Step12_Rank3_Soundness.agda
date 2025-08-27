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
-- 0 · Tiny β-lemma for 'if'
----------------------------------------------------------------------

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- 1 · Unfolding lemma for rank3? on lists with ≥ 3 elements
--     (matches the definition of rank3Witness / rank3? in Step 11)
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
-- 2 · Stripping lemma for the false-branch
--     If nonZeroℤ(det3 u v w) ≡ false and rank3? (u v w rs) ≡ true,
--     then rank3? (v w rs) ≡ true.
----------------------------------------------------------------------

stripFalse :
  ∀ {u v w rs}
  → nonZeroℤ (det3 u v w) ≡ false
  → rank3? (u ∷ v ∷ w ∷ rs) ≡ true
  → rank3? (v ∷ w ∷ rs) ≡ true
stripFalse {u} {v} {w} {rs} eqFalse pr =
  let
    -- unfold to conditional form
    pr-cond :
      (if nonZeroℤ (det3 u v w) then true else rank3? (v ∷ w ∷ rs)) ≡ true
    pr-cond = trans (sym (rank3?-cons u v w rs)) pr

    -- substitute the 'false' equality
    pr-false :
      (if false then true else rank3? (v ∷ w ∷ rs)) ≡ true
    pr-false =
      subst (λ b → (if b then true else rank3? (v ∷ w ∷ rs)) ≡ true)
            eqFalse
            pr-cond
  in
    -- β-reduce to the else-branch
    trans (sym (if-false-β true (rank3? (v ∷ w ∷ rs)))) pr-false

----------------------------------------------------------------------
-- 3 · Soundness: rank3? xs ≡ true  ⇒  HasGoodTriple xs
----------------------------------------------------------------------

soundness : ∀ xs → rank3? xs ≡ true → HasGoodTriple xs
-- Lists of length < 3: impossible, since rank3? reduces to false.
soundness []          ()
soundness (_ ∷ [])    ()
soundness (_ ∷ _ ∷ []) ()

-- Main case: split first on the list shape (makes decrease explicit),
-- then on the Bool decision. Recursion only on (v ∷ w ∷ rs).
soundness (u ∷ v ∷ w ∷ rs) pr with nonZeroℤ (det3 u v w)
... | true  = here {u = u} {v = v} {w = w} {rs = rs} refl
... | false = there (soundness (v ∷ w ∷ rs) (stripFalse refl pr))

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
