{-# OPTIONS --safe #-}

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Structures.Step2_VectorOperations using (Dist)

open import Structures.Step11_Rank3 public using
  ( ℤ³ ; det3 ; nonZeroℤ
  ; Maybe ; just ; nothing ; isJust ; rank3Witness
  ; HasGoodTriple ; here ; there
  )

-- Inspect + β
data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} → (x : A) → Inspect x
inspect x = it x refl

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

-- Unfolding
isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
    ≡ (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

-- Tail vom false-Zweig abziehen
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

-- Soundness (klassischer Fenster-Scan)
witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
witnessSound []          ()
witnessSound (_ ∷ [])    ()
witnessSound (_ ∷ _ ∷ []) ()
witnessSound (u ∷ v ∷ w ∷ rs) pr
  with inspect (nonZeroℤ (det3 u v w))
... | it true  eqTrue  = here  {u = u} {v = v} {w = w} {rs = rs} eqTrue
... | it false eqFalse = there (witnessSound (v ∷ w ∷ rs) (tailFromFalse eqFalse pr))
