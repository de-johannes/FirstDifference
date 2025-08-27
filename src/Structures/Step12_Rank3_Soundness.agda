{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness via Witness
--  Variante: zusätzlich inkrementeller konsekutiver Finder in Step12,
--  damit rank3WitnessInc im Scope ist (keine neuen Module notwendig).
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; _∧_; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

-- Dist nur nötig, wenn du History-Corollarien ergänzen willst.
open import Structures.Step2_VectorOperations using (Dist)

-- Import aus Step 11
open import Structures.Step11_Rank3 public using
  ( ℤ³ ; mk3 ; x ; y ; z₃
  ; _−ℤ_ ; _∗ℤ_
  ; isZeroℤ ; nonZeroℤ
  ; det3

  ; GoodTriple ; pack
  ; Maybe ; just ; nothing ; isJust

  ; HasGoodTriple ; here ; there
  ; rank3Witness
  )

----------------------------------------------------------------------
-- 0 · Inspect-Tool und β-Lemmata für if
----------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} → (x : A) → Inspect x
inspect x = it x refl

if-true-β  : ∀ {A : Set} (x y : A) → (if true  then x else y) ≡ x
if-true-β  x y = refl

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- 1 · (Alt) Unfolding & Soundness für den klassischen Fenster-Scan
----------------------------------------------------------------------

isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
    ≡ (if nonZeroℤ (det3 u v w)
        then true
        else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

tailFromFalse :
  ∀ {u v w rs} →
  nonZeroℤ (det3 u v w) ≡ false →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs)) ≡ true →
  isJust (rank3Witness (v ∷ w ∷ rs)) ≡ true
tailFromFalse {u} {v} {w} {rs} eqFalse pr =
  let
    pr-cond :
      (if nonZeroℤ (det3 u v w)
         then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-cond = trans (sym (isJust-cons u v w rs)) pr

    pr-false :
      (if false then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-false =
      subst (λ b → (if b then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true)
            eqFalse pr-cond
  in
    trans (sym (if-false-β true (isJust (rank3Witness (v ∷ w ∷ rs))))) pr-false

witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
witnessSound []          ()
witnessSound (_ ∷ [])    ()
witnessSound (_ ∷ _ ∷ []) ()
witnessSound (u ∷ v ∷ w ∷ rs) pr
  with inspect (nonZeroℤ (det3 u v w))
... | it true  eqTrue  = here {u = u} {v = v} {w = w} {rs = rs} eqTrue
... | it false eqFalse = there (witnessSound (v ∷ w ∷ rs) (tailFromFalse eqFalse pr))

----------------------------------------------------------------------
-- 2 · Neu: Inkrementeller konsekutiver Finder in Step12
----------------------------------------------------------------------

-- Kreuzprodukt und Kollinearität
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

private
  rank3FromPair : ℤ³ → ℤ³ → List ℤ³ → Maybe GoodTriple
  rank3FromPair a b [] = nothing
  rank3FromPair a b (w ∷ rs) with nonZeroℤ (det3 a b w)
  ... | true  = just (pack a b w rs)
  ... | false with pairGood b w
  ... | true  = rank3FromPair b w rs
  ... | false = rank3WitnessInc (b ∷ w ∷ rs)

-- Öffentlicher inkrementeller Finder (konsekutive Tripel)
rank3WitnessInc : List ℤ³ → Maybe GoodTriple
rank3WitnessInc (u ∷ v ∷ w ∷ rs) with pairGood u v
... | true  with nonZeroℤ (det3 u v w)
... | true  | true  = just (pack u v w rs)
... | true  | false = rank3FromPair u v (w ∷ rs)
... | false         = rank3WitnessInc (v ∷ w ∷ rs)
rank3WitnessInc _ = nothing

rank3?Inc : List ℤ³ → Bool
rank3?Inc xs = isJust (rank3WitnessInc xs)

-- Unfolding-Lemmas für isJust der neuen Funktionen
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
-- 3 · Soundness für den inkrementellen konsekutiven Finder
--    (nur with/inspect, keine case-Lambdas)
----------------------------------------------------------------------

witnessFromPairSound :
  ∀ a b ws → isJust (rank3FromPair a b ws) ≡ true → HasGoodTriple (a ∷ b ∷ ws)
witnessFromPairSound a b [] ()
witnessFromPairSound a b (w ∷ rs) pr =
  let
    pr0 :
      (if nonZeroℤ (det3 a b w)
         then true
         else if pairGood b w
                then isJust (rank3FromPair b w rs)
                else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true
    pr0 = trans (sym (isJust-fromPair-cons a b w rs)) pr
  in
  -- split auf det
  let detObs = inspect (nonZeroℤ (det3 a b w)) in
  case1 detObs
  where
    case1 : Inspect (nonZeroℤ (det3 a b w)) → HasGoodTriple (a ∷ b ∷ w ∷ rs)
    case1 (it true eqDet)  = here {u = a} {v = b} {w = w} {rs = rs} eqDet
    case1 (it false eqDetFalse) =
      let
        pr1 :
          (if pairGood b w
             then isJust (rank3FromPair b w rs)
             else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true
        pr1 =
          trans
            (subst (λ b →
              (if b then true else
                 (if pairGood b w
                    then isJust (rank3FromPair b w rs)
                    else isJust (rank3WitnessInc (b ∷ w ∷ rs)))) ≡ true)
                   eqDetFalse pr0)
            (if-false-β true
               (if pairGood b w
                   then isJust (rank3FromPair b w rs)
                   else isJust (rank3WitnessInc (b ∷ w ∷ rs))))
        pgObs = inspect (pairGood b w)
      in case2 pgObs pr1

    case2 :
      Inspect (pairGood b w) →
      ((if pairGood b w
           then isJust (rank3FromPair b w rs)
           else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true) →
      HasGoodTriple (a ∷ b ∷ w ∷ rs)
    case2 (it true eqPG) pr1 =
      let
        pr-next :
          isJust (rank3FromPair b w rs) ≡ true
        pr-next =
          trans
            (sym (if-true-β (isJust (rank3FromPair b w rs))
                             (isJust (rank3WitnessInc (b ∷ w ∷ rs)))))
            (subst (λ b → (if b then isJust (rank3FromPair b w rs)
                             else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true)
                   eqPG pr1)
        ih : HasGoodTriple (b ∷ w ∷ rs)
        ih = witnessFromPairSound b w rs pr-next
      in there ih

    case2 (it false eqPG) pr1 =
      let
        pr-tail :
          isJust (rank3WitnessInc (b ∷ w ∷ rs)) ≡ true
        pr-tail =
          trans
            (sym (if-false-β (isJust (rank3FromPair b w rs))
                             (isJust (rank3WitnessInc (b ∷ w ∷ rs)))))
            (subst (λ b → (if b then isJust (rank3FromPair b w rs)
                             else isJust (rank3WitnessInc (b ∷ w ∷ rs))) ≡ true)
                   eqPG pr1)
        ih : HasGoodTriple (b ∷ w ∷ rs)
        ih = witnessSoundInc (b ∷ w ∷ rs) pr-tail
      in there ih

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
    pgObs   = inspect (pairGood u v)
  in
  case0 pgObs
  where
    case0 : Inspect (pairGood u v) → HasGoodTriple (u ∷ v ∷ w ∷ rs)
    case0 (it true eqPG) =
      let
        inner :
          (if nonZeroℤ (det3 u v w)
             then true
             else isJust (rank3FromPair u v (w ∷ rs))) ≡ true
        inner =
          trans
            (subst (λ b → (if b
                            then (if nonZeroℤ (det3 u v w)
                                    then true
                                    else isJust (rank3FromPair u v (w ∷ rs)))
                            else isJust (rank3WitnessInc (v ∷ w ∷ rs))) ≡ true)
                   eqPG pr-cond)
            (if-true-β
               (if nonZeroℤ (det3 u v w)
                   then true
                   else isJust (rank3FromPair u v (w ∷ rs)))
               (isJust (rank3WitnessInc (v ∷ w ∷ rs))))
        detObs = inspect (nonZeroℤ (det3 u v w))
      in case1 detObs inner

    case0 (it false eqPG) =
      let
        pr-tail :
          isJust (rank3WitnessInc (v ∷ w ∷ rs)) ≡ true
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
                   eqPG pr-cond)
        ih : HasGoodTriple (v ∷ w ∷ rs)
        ih = witnessSoundInc (v ∷ w ∷ rs) pr-tail
      in there ih

    case1 :
      Inspect (nonZeroℤ (det3 u v w)) →
      ((if nonZeroℤ (det3 u v w)
          then true
          else isJust (rank3FromPair u v (w ∷ rs))) ≡ true) →
      HasGoodTriple (u ∷ v ∷ w ∷ rs)
    case1 (it true eqDet) _ =
      here {u = u} {v = v} {w = w} {rs = rs} eqDet
    case1 (it false eqDetF) inner =
      let
        pr-next :
          isJust (rank3FromPair u v (w ∷ rs)) ≡ true
        pr-next =
          trans
            (sym (if-false-β true (isJust (rank3FromPair u v (w ∷ rs)))))
            (subst (λ b → (if b then true else isJust (rank3FromPair u v (w ∷ rs))) ≡ true)
                   eqDetF inner)
      in witnessFromPairSound u v (w ∷ rs) pr-next
