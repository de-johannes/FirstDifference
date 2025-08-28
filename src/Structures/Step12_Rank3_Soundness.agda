{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness
--  * Gegenrichtung zu Step 11:
--      rank3? xs ≡ true  ⇒  HasGoodTriple xs
--  * plus: Slice-Variante auf dem DriftGraph (via Step 10/11)
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool      using (Bool; true; false; if_then_else_; not)
open import Data.Nat       using (ℕ; zero; suc)
open import Data.List      using (List; []; _∷_; map)
open import Data.Sum       using (_⊎_; inj₁; inj₂)

-- Aus Step 11 holen wir genau die benötigten Bausteine:
open import Structures.Step11_Rank3 using
  ( ℤ ; ℤ³ ; mk3
  ; nonZeroℤ
  ; det3
  ; diffs
  ; GoodTriple ; HasGoodTriple ; here ; there
  ; rank3?     -- Bool-Checker
  ; toZ3
  )

-- Für die Slice-Variante nutzen wir Step 10:
open import Structures.Step7_DriftGraph  using (DriftGraph)
open import Structures.Step10_FoldMap    using (Embed3NatAt)

----------------------------------------------------------------------
-- 0) Lokaler Entscheider für nonZero(det3 u v w)
--    (da Step 11 ihn nicht exportiert)
----------------------------------------------------------------------

decNonZeroDet3 :
  (u v w : ℤ³) →
  (nonZeroℤ (det3 u v w) ≡ true) ⊎ (nonZeroℤ (det3 u v w) ≡ false)
decNonZeroDet3 u v w with nonZeroℤ (det3 u v w)
... | true  = inj₁ refl
... | false = inj₂ refl

----------------------------------------------------------------------
-- 1) Soundness auf Listenebene
--    Idee: Entfalte rank3? / rank3Witness am Kopf-Triple.
--          Falls det ≠ 0: "here". Falls det = 0: reduziere auf Tail und nutze Induktion.
----------------------------------------------------------------------

soundness : ∀ (xs : List ℤ³) → rank3? xs ≡ true → HasGoodTriple xs
-- Längen < 3: unmöglich, da rank3? = false per Definition
soundness []           ()
soundness (_ ∷ [])     ()
soundness (_ ∷ _ ∷ []) ()

-- Hauptfall: mindestens drei Punkte
soundness (u ∷ v ∷ w ∷ rs) pr with decNonZeroDet3 u v w
... | inj₁ hTrue  = here hTrue
... | inj₂ hFalse
  -- Im false-Zweig reduziert rank3? (u∷v∷w∷rs) definitorisch zu rank3? (v∷w∷rs).
  -- Das erzwingen wir per rewrite; dann passt 'pr' exakt als Induktionsvoraussetzung.
  rewrite hFalse = there (soundness (v ∷ w ∷ rs) pr)

----------------------------------------------------------------------
-- 2) Soundness relativ zum Zeit-Slice eines DriftGraphen
--    Wir konstruieren die ℤ³-Punkte wie in Step 11 und wenden soundness auf deren Diffs an.
----------------------------------------------------------------------

soundnessOnSlice :
  (G : DriftGraph) (t : ℕ) →
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  rank3? (diffs ptsZ) ≡ true → HasGoodTriple (diffs ptsZ)
soundnessOnSlice G t pr =
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  soundness (diffs ptsZ) pr
