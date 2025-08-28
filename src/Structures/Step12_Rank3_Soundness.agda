{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness
--  * Gegenrichtung zu Step 11:
--      rank3? xs ≡ true  ⇒  HasGoodTriple xs
--  * plus: Slice-Variante auf dem DriftGraph (via Step 10/11)
--  * TERMINIEREND per Maß (Länge der Liste)
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)
open import Data.Bool      using (Bool; true; false; if_then_else_; not)
open import Data.Nat       using (ℕ; zero; suc)
open import Data.List      using (List; []; _∷_; map; length)
open import Data.Sum       using (_⊎_; inj₁; inj₂)

-- Aus Step 11 holen wir die benötigten Bausteine:
open import Structures.Step11_Rank3 using
  ( ℤ ; ℤ³ ; mk3
  ; nonZeroℤ
  ; det3
  ; diffs
  ; GoodTriple ; HasGoodTriple ; here ; there
  ; rank3?     -- Bool-Checker (isJust ∘ rank3Witness)
  ; toZ3
  )

-- Für die Slice-Variante nutzen wir Step 10:
open import Structures.Step7_DriftGraph  using (DriftGraph)
open import Structures.Step10_FoldMap    using (Embed3NatAt)

----------------------------------------------------------------------
-- 0) Lokaler Entscheider für nonZero(det3 u v w)
----------------------------------------------------------------------

decNonZeroDet3 :
  (u v w : ℤ³) →
  (nonZeroℤ (det3 u v w) ≡ true) ⊎ (nonZeroℤ (det3 u v w) ≡ false)
decNonZeroDet3 u v w with nonZeroℤ (det3 u v w)
... | true  = inj₁ refl
... | false = inj₂ refl

----------------------------------------------------------------------
-- 1) Reduktionslemma für den Checker (definitorisch)
--    Wenn nonZero(det3 u v w) = false, dann verschiebt sich das Fenster.
----------------------------------------------------------------------

rank3?-step :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  nonZeroℤ (det3 u v w) ≡ false →
  rank3? (u ∷ v ∷ w ∷ rs) ≡ rank3? (v ∷ w ∷ rs)
rank3?-step u v w rs hFalse rewrite hFalse = refl

----------------------------------------------------------------------
-- 2) Soundness per Maß (Länge der Liste)
--    Hilfsfunktion soundness′ mit Fuel-Parameter k.
--    Bei jedem Shift auf (v ∷ w ∷ rs) wird k strikt dekrementiert.
----------------------------------------------------------------------

soundness′ : ∀ (xs : List ℤ³) (k : ℕ) → rank3? xs ≡ true → HasGoodTriple xs
-- Listen kürzer als 3: unmöglich, da rank3? ≡ false
soundness′ []           _ ()
soundness′ (_ ∷ [])     _ ()
soundness′ (_ ∷ _ ∷ []) _ ()

-- Hauptfall: mindestens drei Punkte, Fuel muss vorhanden sein
soundness′ (u ∷ v ∷ w ∷ rs) zero       pr = ⊥-elim impossible
  where
    -- unreachable: bei Länge ≥ 3 wählen wir in der Hülle k = length xs ≥ 3
    data ⊥ : Set where
    ⊥-elim : ⊥ → {A : Set} → A
    ⊥-elim ()
    impossible : ⊥
    impossible = case pr of λ ()  -- Rank-Checker kann hier nicht true sein
soundness′ (u ∷ v ∷ w ∷ rs) (suc k) pr with decNonZeroDet3 u v w
... | inj₁ hTrue  = here hTrue
... | inj₂ hFalse =
  let step : rank3? (u ∷ v ∷ w ∷ rs) ≡ rank3? (v ∷ w ∷ rs)
      step = rank3?-step u v w rs hFalse

      pr′  : rank3? (v ∷ w ∷ rs) ≡ true
      pr′  = trans (sym step) pr
  in  there (soundness′ (v ∷ w ∷ rs) k pr′)

-- Öffentliche Hülle ohne Fuel: nimmt k = length xs
soundness : ∀ (xs : List ℤ³) → rank3? xs ≡ true → HasGoodTriple xs
soundness xs pr = soundness′ xs (length xs) pr

----------------------------------------------------------------------
-- 3) Soundness relativ zum Zeit-Slice eines DriftGraphen
----------------------------------------------------------------------

soundnessOnSlice :
  (G : DriftGraph) (t : ℕ) →
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  rank3? (diffs ptsZ) ≡ true → HasGoodTriple (diffs ptsZ)
soundnessOnSlice G t pr =
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  soundness (diffs ptsZ) pr
