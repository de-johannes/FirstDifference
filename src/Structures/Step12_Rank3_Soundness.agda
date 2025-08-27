{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness (Bool ⇒ Spec) and History corollaries
--            Uses the Step 11 checker and spec; no postulates.
--  Final version: explicit structural recursion on 'n' combined
--                 with 'inspect' for a fully sound and terminating proof.
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.Nat       using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
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
-- 3 · Stripping lemma for the false-branch
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
    pr-cond :
      (if nonZeroℤ (det3 u v w) then true else rank3? (v ∷ w ∷ rs)) ≡ true
    pr-cond = trans (sym (rank3?-cons u v w rs)) pr

    pr-false :
      (if false then true else rank3? (v ∷ w ∷ rs)) ≡ true
    pr-false =
      subst (λ b → (if b then true else rank3? (v ∷ w ∷ rs)) ≡ true)
            eqFalse
            pr-cond
  in
    trans (sym (if-false-β true (rank3? (v ∷ w ∷ rs)))) pr-false

----------------------------------------------------------------------
-- 4 · Soundness with an explicit length parameter (structural recursion)
----------------------------------------------------------------------

soundnessLen : ∀ (n : ℕ) (xs : List ℤ³) →
               length xs ≡ n →
               rank3? xs ≡ true →
               HasGoodTriple xs

-- n = 0
soundnessLen zero []       _   ()
soundnessLen zero (_ ∷ _)  ()

-- n = 1
soundnessLen (suc zero) []           ()
soundnessLen (suc zero) (_ ∷ [])     _  ()
soundnessLen (suc zero) (_ ∷ _ ∷ _)  ()

-- n = 2
soundnessLen (suc (suc zero)) []              ()
soundnessLen (suc (suc zero)) (_ ∷ [])        ()
soundnessLen (suc (suc zero)) (_ ∷ _ ∷ [])      _  ()
soundnessLen (suc (suc zero)) (_ ∷ _ ∷ _ ∷ _)  ()

-- n ≥ 3, but list too short (impossible by length equation)
soundnessLen (suc (suc (suc n′))) []              ()
soundnessLen (suc (suc (suc n′))) (_ ∷ [])        ()
soundnessLen (suc (suc (suc n′))) (_ ∷ _ ∷ [])      ()

-- Main case: n ≥ 3 and xs has at least 3 elements
soundnessLen (suc (suc (suc n′))) (u ∷ v ∷ w ∷ rs) refl pr
  with inspect (nonZeroℤ (det3 u v w))
... | it true eqT =
      -- Case 1: The determinant is non-zero.
      -- 'inspect' provides the proof 'eqT', which we use for 'here'.
      here eqT
... | it false eqF =
      -- Case 2: The determinant is zero.
      -- 'inspect' provides the proof 'eqF'. We use it to strip the head
      -- and recurse on a structurally smaller number 'n′'.
      let pr-tail = stripFalse eqF pr
      in there (soundnessLen (suc (suc n′)) (v ∷ w ∷ rs) refl pr-tail)

----------------------------------------------------------------------
-- 5 · Public soundness (derives 'n' from length xs, then calls soundnessLen)
----------------------------------------------------------------------

soundness : ∀ xs → rank3? xs ≡ true → HasGoodTriple xs
soundness xs pr = soundnessLen (length xs) xs refl pr

----------------------------------------------------------------------
-- 6 · Soundness specialized to histories
----------------------------------------------------------------------

soundnessOnHistory :
  ∀ {n} (hist : List (Dist n)) →
  rank3OnHistoryBool hist ≡ true →
  HasGoodTriple (diffs (FoldMap³ {n} hist))
soundnessOnHistory {n} hist pr =
  soundness (diffs (FoldMap³ {n} hist)) pr

----------------------------------------------------------------------
-- 7 · Convenience re-exports (pair the two directions)
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
