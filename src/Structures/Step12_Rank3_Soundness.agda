{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness via Witness
--  Idea: Separate computation and proof.
--        We prove:  if isJust (rank3Witness xs) ≡ true
--        then xs contains a good triple (HasGoodTriple xs).
--  No postulates. No sized types. Pure structural recursion on the list.
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

-- Dist is only needed for potential history lemmas later; keep import light.
open import Structures.Step2_VectorOperations using (Dist)

-- Import exactly what we need from Step 11 (witness + spec constructors).
open import Structures.Step11_Rank3 public using
  ( ℤ³
  ; det3
  ; nonZeroℤ

  ; Maybe               -- witness carrier
  ; just
  ; nothing
  ; isJust              -- witness-to-Bool projection
  ; rank3Witness        -- the PROGRAM: scans the list and returns a witness if found

  ; HasGoodTriple       -- the SPEC: logical property “there exists a good triple”
  ; here                -- constructor: immediate triple at the head (needs proof cond ≡ true)
  ; there               -- constructor: witness is in the tail
  ; pack                -- packages (u v w rs) into a GoodTriple; used by rank3Witness’ definition
  )

----------------------------------------------------------------------
-- 0 · Tiny β-lemma for 'if' with false (handy for tail extraction)
----------------------------------------------------------------------

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- 1 · Unfolding lemma for the WITNESS (non-recursive)
--    How 'isJust ∘ rank3Witness' behaves on lists of length ≥ 3.
--    This matches the Step 11 definition:
--      rank3Witness (u∷v∷w∷rs) =
--        if nonZeroℤ (det3 u v w)
--        then just (pack u v w rs)
--        else rank3Witness (v ∷ w ∷ rs)
----------------------------------------------------------------------

isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
  ≡ (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl   -- LHS reduces to isJust (just …) ≡ true; RHS reduces to if true then true else … ≡ true
... | false = refl   -- LHS reduces to isJust (rank3Witness tail); RHS to if false then true else … ≡ isJust tail

----------------------------------------------------------------------
-- 2 · Tail extraction: from a 'false' guard we get a tail proof
--    If nonZeroℤ(det3 u v w) ≡ false and the head-branch yields true overall,
--    then the tail projection must be true as well.
----------------------------------------------------------------------

tailFromFalse :
  ∀ {u v w rs} →
  nonZeroℤ (det3 u v w) ≡ false →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs)) ≡ true →
  isJust (rank3Witness (v ∷ w ∷ rs)) ≡ true
tailFromFalse {u} {v} {w} {rs} eqFalse pr =
  let
    -- Move to the conditional shape using the unfolding lemma:
    pr-cond :
      (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-cond = trans (sym (isJust-cons u v w rs)) pr

    -- Substitute b = false into the guard:
    pr-false :
      (if false then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-false =
      subst (λ b → (if b then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true)
            eqFalse
            pr-cond
  in
    -- β-reduce the false-branch and finish:
    trans (sym (if-false-β true (isJust (rank3Witness (v ∷ w ∷ rs))))) pr-false

----------------------------------------------------------------------
-- 3 · Main theorem: “witness ⇒ spec”
--    If rank3Witness finds something (isJust ≡ true),
--    then the logical property HasGoodTriple holds.
--    Proof is by plain structural recursion on the list.
----------------------------------------------------------------------

witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
-- Lists of length < 3: rank3Witness ≡ nothing ⇒ isJust ≡ false ⇒ impossible
witnessSound []          ()
witnessSound (_ ∷ [])    ()
witnessSound (_ ∷ _ ∷ []) ()

-- Length ≥ 3: split off the first triple (u,v,w) and the rest rs
witnessSound (u ∷ v ∷ w ∷ rs) pr with nonZeroℤ (det3 u v w)
... | true  =              -- Head already contains a good triple
  here {u = u} {v = v} {w = w} {rs = rs} refl
... | false =              -- Otherwise, the witness lives in the tail
  there (witnessSound (v ∷ w ∷ rs) (tailFromFalse refl pr))
