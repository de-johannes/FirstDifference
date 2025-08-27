{-# OPTIONS --safe #-}

----------------------------------------------------------------------
-- Step 12 ▸ Incremental Rank-3 (consecutive) with constructive witness
--            - hält ein nicht-kollineares Paar als "Basis"
--            - prüft nur konsekutive Tripel (kompatibel zu HasGoodTriple)
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; _∧_; if_then_else_)
open import Data.List      using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

-- Step 2: Dist (für die History-Variante)
open import Structures.Step2_VectorOperations using (Dist)

-- Step 11: ℤ, ℤ³, det3, Maybe & Co., FoldMap³, diffs, GoodTriple, HasGoodTriple …
open import Structures.Step11_Rank3 public using
  ( ℤ ; ℤ³ ; mk3 ; x ; y ; z₃
  ; _+ℤ_ ; _−ℤ_ ; _∗ℤ_
  ; isZeroℤ ; nonZeroℤ
  ; det3

  ; GoodTriple ; pack
  ; Maybe ; just ; nothing ; isJust

  ; HasGoodTriple ; here ; there
  ; FoldMap³ ; diffs
  )

----------------------------------------------------------------------
-- 0 · Inspect-Tool (wie in Step 12): Booleans als Gleichheit b ≡ true/false fassen
----------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} → (x : A) → Inspect x
inspect x = it x refl

-- β-Lemmas für if
if-true-β  : ∀ {A : Set} (x y : A) → (if true  then x else y) ≡ x
if-true-β  x y = refl

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- 1 · Geometrische Hilfen: Kreuzprodukt & (Nicht-)Kollinearität über Bool
----------------------------------------------------------------------

-- Kreuzprodukt in ℤ³
cross3 : ℤ³ → ℤ³ → ℤ³
cross3 a b =
  let ax = x a ; ay = y a ; az = z₃ a
      bx = x b ; by = y b ; bz = z₃ b
      cx = (ay ∗ℤ bz) −ℤ (az ∗ℤ by)
      cy = (az ∗ℤ bx) −ℤ (ax ∗ℤ bz)
      cz = (ax ∗ℤ by) −ℤ (ay ∗ℤ bx)
  in  mk3 cx cy cz

isZero3 : ℤ³ → Bool
isZero3 v = isZeroℤ (x v) ∧ isZeroℤ (y v) ∧ isZeroℤ (z₃ v)

pairGood : ℤ³ → ℤ³ → Bool
pairGood a b = if isZero3 (cross3 a b) then false else true

----------------------------------------------------------------------
-- 2 · Inkrementelle Suche nur über konsekutive Tripel
--     rank3FromPair hält das (gute) Paar (a,b) und testet fortlaufend w.
----------------------------------------------------------------------

private
  rank3FromPair : ℤ³ → ℤ³ → List ℤ³ → Maybe GoodTriple
  rank3FromPair a b [] = nothing
  rank3FromPair a b (w ∷ rs) with nonZeroℤ (det3 a b w)
  ... | true  = just (pack a b w rs)
  ... | false with pairGood b w
  ... | true  = rank3FromPair b w rs
  ... | false = rank3WitnessInc (b ∷ w ∷ rs)

-- Öffentliche Funktion: inkrementeller konsekutiver Zeugenfinder
rank3WitnessInc : List ℤ³ → Maybe GoodTriple
rank3WitnessInc (u ∷ v ∷ w ∷ rs) with pairGood u v
... | true  with nonZeroℤ (det3 u v w)
... | true  | true  = just (pack u v w rs)
... | true  | false = rank3FromPair u v (w ∷ rs)
... | false         = rank3WitnessInc (v ∷ w ∷ rs)
rank3WitnessInc _ = nothing

-- Boolean-Wrapper
rank3?Inc : List ℤ³ → Bool
rank3?Inc xs = isJust (rank3WitnessInc xs)

-- Historien-Variante (wie in Step 11, nur mit inkrementellem Checker)
rank3OnHistoryBoolInc : ∀ {n} → List (Dist n) → Bool
rank3OnHistoryBoolInc {n} hist = rank3?Inc (diffs (FoldMap³ {n} hist))

----------------------------------------------------------------------
-- 3 · Unfolding-Lemmas für isJust (analog Step 12), alles ohne Postulates
----------------------------------------------------------------------

isJust-fromPair-cons :
  ∀ (a b w : ℤ³) (rs : List ℤ³) →
  isJust (rank3FromPair a b (w ∷ rs))
    ≡ (if nonZeroℤ (det3 a b w)
        then true
        else if pairGood b w
               then isJust (rank3FromPair b w rs)
               else isJust (rank3WitnessInc (b ∷ w ∷ rs)))
isJust-fromPair-cons a b w rs with nonZeroℤ (det3 a b w)
... | true  = refl
... | false with pairGood b w
... | true  = refl
... | false = refl

isJust-inc-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3WitnessInc (u ∷ v ∷ w ∷ rs))
    ≡ (if pairGood u v
        then (if nonZeroℤ (det3 u v w)
               then true
               else isJust (rank3FromPair u v (w ∷ rs)))
        else isJust (rank3WitnessInc (v ∷ w ∷ rs)))
isJust-inc-cons u v w rs with pairGood u v
... | true with nonZeroℤ (det3 u v w)
... | true | true  = refl
... | true | false = refl
... | false        = refl

----------------------------------------------------------------------
-- 4 · Soundness: isJust (rank3WitnessInc xs) ≡ true ⇒ HasGoodTriple xs
--     Beweis per struktureller Rekursion, plus Hilfslemma für rank3FromPair
----------------------------------------------------------------------

-- Hilfslemma: Soundness für die innere Schleife (a,b) • ws
witnessFromPairSound :
  ∀ a b ws → isJust (rank3FromPair a b ws) ≡ true → HasGoodTriple (a ∷ b ∷ ws)
witnessFromPairSound a b [] ()
witnessFromPairSound a b (w ∷ rs) pr =
  let
    -- Entfalte isJust anhand der Definition
    pr-cond₀ :
      (if nonZeroℤ (det3 a b w)
         then true
         else if pairGood b w
                then isJust (rank3FromPair b w rs)
                else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true
    pr-cond₀ = trans (sym (isJust-fromPair-cons a b w rs)) pr

    -- unterscheide die Fälle per Inspect, um Gleichheiten zu bekommen
    pg₁ = inspect (nonZeroℤ (det3 a b w))
  in
  case pg₁ of
    λ where
      (it true  eqDet) →
        -- Kopftripel ist gut
        --   if true then true else …  ≡ true  ⇒ sofort 'here' mit Beweis eqDet
        let _ = eqDet in
        here {u = a} {v = b} {w = w} {rs = rs} eqDet

      (it false eqDetFalse) →
        -- det == false; reduziere auf den zweiten if
        let
          pr-cond₁ :
            (if pairGood b w
               then isJust (rank3FromPair b w rs)
               else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true
          pr-cond₁ =
            trans
              (subst (λ b → (if b then true else
                               (if pairGood b w
                                  then isJust (rank3FromPair b w rs)
                                  else isJust (rank3WitnessInc (b ∷ w ∷ rs)))) ≡ true)
                     eqDetFalse
                     pr-cond₀)
              (if-false-β true
                 (if pairGood b w
                     then isJust (rank3FromPair b w rs)
                     else isJust (rank3WitnessInc (b ∷ w ∷ rs))))
          pg₂ = inspect (pairGood b w)
        in case pg₂ of
             λ where
               (it true  eqPG) →
                 -- gutes Paar (b,w): rekursiv auf rank3FromPair b w rs
                 let
                   pr-next :
                     isJust (rank3FromPair b w rs) ≡ true
                   pr-next =
                     trans
                       (sym (if-true-β (isJust (rank3FromPair b w rs))
                                        (isJust (rank3WitnessInc (b ∷ w ∷ rs)))))
                       (subst (λ b → (if b then isJust (rank3FromPair b w rs)
                                        else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true)
                              eqPG
                              pr-cond₁)
                   ih : HasGoodTriple (b ∷ w ∷ rs)
                   ih = witnessFromPairSound b w rs pr-next
                 in there ih

               (it false eqPG) →
                 -- degeneriertes Paar (b,w): wir sind auf dem Tail mit rank3WitnessInc
                 let
                   pr-tail :
                     isJust (rank3WitnessInc (b ∷ w ∷ rs)) ≡ true
                   pr-tail =
                     trans
                       (sym (if-false-β (isJust (rank3FromPair b w rs))
                                        (isJust (rank3WitnessInc (b ∷ w ∷ rs)))))
                       (subst (λ b → (if b then isJust (rank3FromPair b w rs)
                                        else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true)
                              eqPG
                              pr-cond₁)
                   ih : HasGoodTriple (b ∷ w ∷ rs)
                   ih = witnessSoundInc (b ∷ w ∷ rs) pr-tail
                 in there ih

-- Hauptsatz: Soundness des inkrementellen konsekutiven Finders
witnessSoundInc : ∀ xs → isJust (rank3WitnessInc xs) ≡ true → HasGoodTriple xs
witnessSoundInc []          ()
witnessSoundInc (_ ∷ [])    ()
witnessSoundInc (_ ∷ _ ∷ []) ()
witnessSoundInc (u ∷ v ∷ w ∷ rs) pr =
  let
    pr-cond :
      (if pairGood u v
         then (if nonZeroℤ (det3 u v w)
                then true
                else isJust (rank3FromPair u v (w ∷ rs)))
         else isJust (rank3WitnessInc (v ∷ w ∷ rs))) ≡ true
    pr-cond = trans (sym (isJust-inc-cons u v w rs)) pr

    pg₀ = inspect (pairGood u v)
  in
  case pg₀ of
    λ where
      (it true eqPG) →
        -- Reduktion auf inneren if
        let
          pr-cond' :
            (if nonZeroℤ (det3 u v w)
               then true
               else isJust (rank3FromPair u v (w ∷ rs))) ≡ true
          pr-cond' =
            trans
              (subst (λ b → (if b
                              then (if nonZeroℤ (det3 u v w)
                                      then true
                                      else isJust (rank3FromPair u v (w ∷ rs)))
                              else isJust (rank3WitnessInc (v ∷ w ∷ rs))) ≡ true)
                     eqPG
                     pr-cond)
              (if-true-β
                 (if nonZeroℤ (det3 u v w)
                     then true
                     else isJust (rank3FromPair u v (w ∷ rs)))
                 (isJust (rank3WitnessInc (v ∷ w ∷ rs))))
          pg₁ = inspect (nonZeroℤ (det3 u v w))
        in case pg₁ of
             λ where
               (it true  eqDet) →
                 -- Kopftripel ist gut
                 here {u = u} {v = v} {w = w} {rs = rs} eqDet
               (it false eqDetFalse) →
                 -- det==false → Soundness der inneren Schleife ab (u,v)
                 let
                   pr-next :
                     isJust (rank3FromPair u v (w ∷ rs)) ≡ true
                   pr-next =
                     trans
                       (sym (if-false-β true (isJust (rank3FromPair u v (w ∷ rs)))))
                       (subst (λ b → (if b then true else isJust (rank3FromPair u v (w ∷ rs))) ≡ true)
                              eqDetFalse
                              pr-cond')
                 in witnessFromPairSound u v (w ∷ rs) pr-next

      (it false eqPG) →
        -- erstes Paar degeneriert → Soundness auf Tail
        let
          pr-tail : isJust (rank3WitnessInc (v ∷ w ∷ rs)) ≡ true
          pr-tail =
            trans
              (sym (if-false-β (if nonZeroℤ (det3 u v w)
                                  then true
                                  else isJust (rank3FromPair u v (w ∷ rs)))
                               (isJust (rank3WitnessInc (v ∷ w ∷ rs)))))
              (subst (λ b → (if b
                              then (if nonZeroℤ (det3 u v w)
                                      then true
                                      else isJust (rank3FromPair u v (w ∷ rs)))
                              else isJust (rank3WitnessInc (v ∷ w ∷ rs))) ≡ true)
                     eqPG
                     pr-cond)
          ih : HasGoodTriple (v ∷ w ∷ rs)
          ih = witnessSoundInc (v ∷ w ∷ rs) pr-tail
        in there ih
