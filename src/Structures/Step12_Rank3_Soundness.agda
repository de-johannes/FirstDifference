{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness via Witness
--  Idea: Separate computation and proof.
--        We prove: if isJust (rank3Witness xs) ≡ true
--        then xs contains a good triple (HasGoodTriple xs).
--  No postulates. Pure structural recursion on the list.
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

-- Dist only needed if you add history corollaries later.
open import Structures.Step2_VectorOperations using (Dist)

-- We import exactly what we need from Step 11.
open import Structures.Step11_Rank3 public using
  ( ℤ³
  ; det3
  ; nonZeroℤ

  ; Maybe               -- witness carrier
  ; just
  ; nothing
  ; isJust              -- Bool projection from Maybe
  ; rank3Witness        -- PROGRAM: scans list, returns witness if found

  ; HasGoodTriple       -- SPEC: logical property “there exists a good triple”
  ; here                -- constructor: head triple is good (needs equality proof)
  ; there               -- constructor: witness lives in the tail
  ; pack                -- packaging used by rank3Witness (not used here directly)
  )

----------------------------------------------------------------------
-- 0 · Inspect utility (capture equality from a decision)
----------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} → (x : A) → Inspect x
inspect x = it x refl

----------------------------------------------------------------------
-- 1 · Tiny β-lemma for 'if' with false
----------------------------------------------------------------------

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- 2 · Unfolding lemma for the WITNESS (non-recursive)
--    Behaviour of isJust (rank3Witness ...) on length ≥ 3.
----------------------------------------------------------------------

isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
  ≡ (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

----------------------------------------------------------------------
-- 3 · Tail extraction for the false branch
----------------------------------------------------------------------

tailFromFalse :
  ∀ {u v w rs} →
  nonZeroℤ (det3 u v w) ≡ false →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs)) ≡ true →
  isJust (rank3Witness (v ∷ w ∷ rs)) ≡ true
tailFromFalse {u} {v} {w} {rs} eqFalse pr =
  let
    pr-cond :
      (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-cond = trans (sym (isJust-cons u v w rs)) pr

    pr-false :
      (if false then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-false =
      subst (λ b → (if b then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true)
            eqFalse
            pr-cond
  in
    trans (sym (if-false-β true (isJust (rank3Witness (v ∷ w ∷ rs))))) pr-false

----------------------------------------------------------------------
-- 4 · Main theorem: witness ⇒ spec
--    If rank3Witness finds something (isJust ≡ true),
--    then HasGoodTriple holds. Structural recursion on the list.
----------------------------------------------------------------------

witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
-- Lists of length < 3: rank3Witness ≡ nothing ⇒ isJust ≡ false ⇒ impossible
witnessSound []          ()
witnessSound (_ ∷ [])    ()
witnessSound (_ ∷ _ ∷ []) ()

-- Length ≥ 3
witnessSound (u ∷ v ∷ w ∷ rs) pr
  with inspect (nonZeroℤ (det3 u v w))
... | it true  eqTrue  = here  {u = u} {v = v} {w = w} {rs = rs} eqTrue
... | it false eqFalse = there (witnessSound (v ∷ w ∷ rs) (tailFromFalse eqFalse pr))
