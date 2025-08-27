{-# OPTIONS --safe #-}

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

-- Dist nur nötig, falls History-Korollare ergänzt werden.
open import Structures.Step2_VectorOperations using (Dist)

-- Wir verwenden ausschließlich die Schnittstelle aus Step 11.
open import Structures.Step11_Rank3 public using
  ( ℤ³
  ; det3
  ; nonZeroℤ
  ; Maybe ; just ; nothing ; isJust ; rank3Witness
  ; HasGoodTriple ; here ; there
  )

------------------------------------------------------------------------
-- Hilfs-Lemmas
------------------------------------------------------------------------

-- β-Lemma: „if false …“ vereinfacht definitional
if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

-- Entfaltung der Programmlogik (direkt aus Step 11)
isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
    ≡ (if nonZeroℤ (det3 u v w)
         then true
         else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

-- False-Zweig extrahieren: wenn det=0, muss das 'true' aus dem Tail kommen
tailFromFalse :
  ∀ {u v w rs} →
  nonZeroℤ (det3 u v w) ≡ false →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs)) ≡ true →
  isJust (rank3Witness (v ∷ w ∷ rs)) ≡ true
tailFromFalse {u} {v} {w} {rs} eqFalse pr =
  let
    pr-cond :
      (if nonZeroℤ (det3 u v w)
          then true
          else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-cond = trans (sym (isJust-cons u v w rs)) pr

    pr-false :
      (if false then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-false =
      subst (λ b → (if b then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true)
            eqFalse
            pr-cond
  in
    trans (sym (if-false-β true (isJust (rank3Witness (v ∷ w ∷ rs))))) pr-false

------------------------------------------------------------------------
-- Inspect-Hilfe: Gleichheit zum 'with'-Wert bekommen
------------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} → (x : A) → Inspect x
inspect x = it x refl

------------------------------------------------------------------------
-- Hauptsatz: Soundness für rank3Witness
--  Idee: ein einziges 'with' auf die Beobachtung b, aus der wir die
--  benötigte Gleichheit entwickeln. Keine doppelten withs ⇒ stabil.
------------------------------------------------------------------------

witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
-- Längen < 3: unmöglich
witnessSound []          ()
witnessSound (_ ∷ [])    ()
witnessSound (_ ∷ _ ∷ []) ()

-- Länge ≥ 3: ein einziges with auf die Beobachtung + ihre Gleichheit
witnessSound (u ∷ v ∷ w ∷ rs) pr
  with inspect (nonZeroℤ (det3 u v w))
... | it true  eqTrue  =
      -- Kopftripel ist gut; 'eqTrue' liefert exakt die geforderte Gleichheit
      here {u = u} {v = v} {w = w} {rs = rs} eqTrue

... | it false eqFalse =
      -- det==false → True muss aus dem Tail kommen
      there (witnessSound (v ∷ w ∷ rs) (tailFromFalse eqFalse pr))
