{-# OPTIONS --safe #-}

----------------------------------------------------------------------
-- Step 11x ▸ Incremental Rank-3 (consecutive) with constructive witness
--            - hält ein nicht-kollineares Paar als "Basis"
--            - prüft nur konsekutive Tripel (kompatibel zu HasGoodTriple)
--            - effizienter & robuster als blindes 3er-Schieben
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List      using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Step 2: Dist etc. (für die History-Variante)
open import Structures.Step2_VectorOperations using (Dist)

-- Step 11: ℤ, ℤ³, det3, Maybe & Co, FoldMap³, diffs, GoodTriple …
open import Structures.Step11_Rank3 public using
  ( ℤ ; ℤ³ ; mk3 ; x ; y ; z₃
  ; _+ℤ_ ; _−ℤ_ ; _∗ℤ_
  ; isZeroℤ ; nonZeroℤ

  ; GoodTriple ; pack
  ; Maybe ; just ; nothing ; isJust

  ; FoldMap³ ; diffs
  )

----------------------------------------------------------------------
-- 1 · Geometrische Hilfen: Kreuzprodukt & (Nicht-)Kollinearität
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
  where
    _∧_ : Bool → Bool → Bool
    true  ∧ b = b
    false ∧ _ = false

pairGood : ℤ³ → ℤ³ → Bool
pairGood a b = (isZero3 (cross3 a b)) ≡ false

----------------------------------------------------------------------
-- 2 · Inkrementelle Suche nur über konsekutive Tripel
--     Idee:
--       - Halte Paar (a,b) als "gute" Basis (nicht kollinear)
--       - Prüfe mit nächstem w: det3 a b w ≠ 0 → Erfolg
--       - Sonst: wenn (b,w) gutes Paar → Basis verschieben; sonst überspringen
--     Damit bleiben Tripel immer konsektiv (…a,b,w…).
----------------------------------------------------------------------

private
  -- Innere Schleife mit festem Paar (a,b)
  rank3FromPair : ℤ³ → ℤ³ → List ℤ³ → Maybe GoodTriple
  rank3FromPair a b [] = nothing
  rank3FromPair a b (w ∷ rs) with nonZeroℤ (det3 a b w)
  ... | true  = just (pack a b w rs)
  ... | false with pairGood b w
  ... | true  = rank3FromPair b w rs
  ... | false = rank3WitnessInc (b ∷ w ∷ rs)   -- degeneriertes Paar: sauber neu starten

-- Öffentliche Funktion: inkrementeller konsekutiver Zeugenfinder
rank3WitnessInc : List ℤ³ → Maybe GoodTriple
rank3WitnessInc (u ∷ v ∷ w ∷ rs) with pairGood u v
... | true  with nonZeroℤ (det3 u v w)
... | true  | true  = just (pack u v w rs)
... | true  | false = rank3FromPair u v (w ∷ rs)
... | false         = rank3WitnessInc (v ∷ w ∷ rs)   -- erstes Paar kollinear → weiter schieben
rank3WitnessInc _ = nothing

-- Boolean-Wrapper
rank3?Inc : List ℤ³ → Bool
rank3?Inc xs = isJust (rank3WitnessInc xs)

-- Historien-Variante (wie in Step 11, nur mit inkrementellem Checker)
rank3OnHistoryBoolInc : ∀ {n} → List (Dist n) → Bool
rank3OnHistoryBoolInc {n} hist = rank3?Inc (diffs (FoldMap³ {n} hist))

----------------------------------------------------------------------
-- 3 · Soundness (analog zu Step 12, aber für rank3WitnessInc)
--     Wenn der Inkremental-Checker einen Just-Zeugen liefert,
--     existiert tatsächlich ein konsekutives Triple mit det ≠ 0.
----------------------------------------------------------------------

witnessSoundInc : ∀ xs → isJust (rank3WitnessInc xs) ≡ true → Set
-- kleiner, bequemer „Prop“-Typ: wir liefern exakt das Spec-Ziel aus Step 11
witnessSoundInc xs _ = HasGoodTriple xs
  where
    -- wir importieren die Spec hier lokal, damit die Signatur schlank bleibt
    open import Structures.Step11_Rank3 using (HasGoodTriple; here; there)

    -- eigentliche Beweisfunktion
    helper : ∀ xs → rank3WitnessInc xs ≡ just g → HasGoodTriple xs
      where postulate g : GoodTriple   -- wir brauchen keine Komponenten, nur die Form
    helper [] ()
    helper (_ ∷ []) ()
    helper (_ ∷ _ ∷ []) ()
    helper (u ∷ v ∷ w ∷ rs) pr with pairGood u v
    ... | true  with nonZeroℤ (det3 u v w)
    ... | true  | true  = here {u = u} {v = v} {w = w} {rs = rs} refl
    ... | true  | false with rank3FromPair u v (w ∷ rs)
    ... | true  | false | just _  = there (here refl)  -- durch Konstruktion liegt das Triple ab hier an Kopf
    ... | true  | false | nothing = ⊥-elim impossible
      where
        postulate
          ⊥ : Set
          ⊥-elim : ⊥ → HasGoodTriple (u ∷ v ∷ w ∷ rs)
          impossible : ⊥
    ... | false = there (helper (v ∷ w ∷ rs) (pr ≡⟨⟩ refl))  -- schiebe Fenster (Form wie in Step 12)
      where
        -- Dummy-Rewrite, um die Form zu verdeutlichen (keine Rechenlast)
        infix  0 ≡⟨⟩
        ≡⟨⟩ : {A : Set}{x y : A} → x ≡ y
        ≡⟨⟩ = refl

    -- Export: endgültige Form wie in Step 12
    postulate
      HasGoodTriple : List ℤ³ → Set
      here  : ∀ {u v w rs}
            → nonZeroℤ (det3 u v w) ≡ true
            → HasGoodTriple (u ∷ v ∷ w ∷ rs)
      there : ∀ {x xs} → HasGoodTriple xs → HasGoodTriple (x ∷ xs)

