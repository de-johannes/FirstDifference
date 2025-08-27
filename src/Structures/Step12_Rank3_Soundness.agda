{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness via Witness
--  Idee: Programm/Beweis trennen.
--        Wir zeigen: isJust (rank3Witness xs) ≡ true ⇒ HasGoodTriple xs
--  Keine Postulate. Reine strukturelle Rekursion über die Liste.
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

-- Dist nur nötig, falls später History-Korollare ergänzt werden.
open import Structures.Step2_VectorOperations using (Dist)

-- Import aus Step 11: genau das, was wir brauchen.
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
  ; GoodTriple        -- (für Vollständigkeit; hier nicht direkt verwendet)
  )

----------------------------------------------------------------------
-- 0 · Inspect-Hilfstyp (Erfassen einer Gleichheit aus einer Entscheidung)
----------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} → (x : A) → Inspect x
inspect x = it x refl

----------------------------------------------------------------------
-- 1 · β-Lemma: 'if false then x else y' ≡ y
----------------------------------------------------------------------

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- 2 · Entfaltungslemma für isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
--     (nicht-rekursiv; folgt direkt aus der Definition in Step 11)
----------------------------------------------------------------------

isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
  ≡ (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

----------------------------------------------------------------------
-- 3 · Schwänzeziehen im false-Zweig
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
-- 4 · Hauptsatz (Soundness): witness ⇒ spec
--     Wenn isJust (rank3Witness xs) ≡ true, dann HasGoodTriple xs.
--     Strukturelle Rekursion über xs.
----------------------------------------------------------------------

witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
-- Längen < 3: unmöglich (rank3Witness ≡ nothing ⇒ isJust ≡ false)
witnessSound []          ()
witnessSound (_ ∷ [])    ()
witnessSound (_ ∷ _ ∷ []) ()

-- Länge ≥ 3
witnessSound (u ∷ v ∷ w ∷ rs) pr
  with inspect (nonZeroℤ (det3 u v w))
... | it true  eqTrue  = here  {u = u} {v = v} {w = w} {rs = rs} eqTrue
... | it false eqFalse = there (witnessSound (v ∷ w ∷ rs) (tailFromFalse eqFalse pr))
