{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness
--  * Gegenrichtung zu Step 11:
--      rank3? xs ≡ true  ⇒  HasGoodTriple xs
--  * plus: Slice-Variante (via Step 10/11)
--  * TERMINIEREND per Maß (Länge der Liste, mit ≤-Beweis)
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Bool      using (Bool; true; false; if_then_else_; not)
open import Data.Nat       using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List      using (List; []; _∷_; map; length)
open import Data.Sum       using (_⊎_; inj₁; inj₂)

-- Aus Step 11: Kernbausteine
open import Structures.Step11_Rank3 using
  ( ℤ ; ℤ³ ; mk3
  ; nonZeroℤ
  ; det3
  ; diffs
  ; GoodTriple ; HasGoodTriple ; here ; there
  ; rank3?     -- Bool-Checker
  ; toZ3
  )

-- Step 10: Punktwolke pro Zeit-Slice
open import Structures.Step7_DriftGraph  using (DriftGraph)
open import Structures.Step10_FoldMap    using (Embed3NatAt)

----------------------------------------------------------------------
-- 0) Entscheider für nonZero(det3 u v w) (lokal)
----------------------------------------------------------------------

decNonZeroDet3 :
  (u v w : ℤ³) →
  (nonZeroℤ (det3 u v w) ≡ true) ⊎ (nonZeroℤ (det3 u v w) ≡ false)
decNonZeroDet3 u v w with nonZeroℤ (det3 u v w)
... | true  = inj₁ refl
... | false = inj₂ refl

----------------------------------------------------------------------
-- 1) Definitorische Verschiebung des Fensters bei det = 0
----------------------------------------------------------------------

rank3?-step :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  nonZeroℤ (det3 u v w) ≡ false →
  rank3? (u ∷ v ∷ w ∷ rs) ≡ rank3? (v ∷ w ∷ rs)
rank3?-step u v w rs hFalse rewrite hFalse = refl

-- Hilfsbeweis: von suc n ≤ suc k auf n ≤ k herunterziehen
tail≤ : ∀ {n k} → suc n ≤ suc k → n ≤ k
tail≤ (s≤s p) = p

-- Länge ≤ Länge (Reflexivität) – level-polymorph!
len≤len : ∀ {a} {A : Set a} (xs : List A) → length xs ≤ length xs
len≤len []       = z≤n
len≤len (_ ∷ xs) = s≤s (len≤len xs)

----------------------------------------------------------------------
-- 2) Soundness mit Maß (Länge xs) als Fuel und Beweis length xs ≤ k
----------------------------------------------------------------------

soundness′ : ∀ (xs : List ℤ³) (k : ℕ)
           → length xs ≤ k
           → rank3? xs ≡ true
           → HasGoodTriple xs
-- Listen < 3: unmöglich, denn rank3? [] / [_] / [_ , _] = false
soundness′ []           _ _  ()
soundness′ (_ ∷ [])     _ _  ()
soundness′ (_ ∷ _ ∷ []) _ _  ()

-- ≥ 3 Punkte, k = 0: unmöglich, da length (u∷v∷w∷rs) = suc (…) ≤ 0 nicht konstruierbar
soundness′ (u ∷ v ∷ w ∷ rs) zero     () pr

-- ≥ 3 Punkte, k = suc k': normaler Beweisschritt
soundness′ (u ∷ v ∷ w ∷ rs) (suc k) le pr with decNonZeroDet3 u v w
... | inj₁ hTrue  = here hTrue
... | inj₂ hFalse =
  let step : rank3? (u ∷ v ∷ w ∷ rs) ≡ rank3? (v ∷ w ∷ rs)
      step = rank3?-step u v w rs hFalse

      pr′  : rank3? (v ∷ w ∷ rs) ≡ true
      pr′  = trans (sym step) pr

      -- length (u ∷ v ∷ w ∷ rs) ≡ suc (length (v ∷ w ∷ rs))
      -- ⇒ tail≤ le : length (v ∷ w ∷ rs) ≤ k
      le′  : length (v ∷ w ∷ rs) ≤ k
      le′  = tail≤ le
  in  there (soundness′ (v ∷ w ∷ rs) k le′ pr′)

-- Öffentliche Hülle: k := length xs und Reflexivität als Beweis
soundness : ∀ (xs : List ℤ³) → rank3? xs ≡ true → HasGoodTriple xs
soundness xs pr = soundness′ xs (length xs) (len≤len xs) pr

----------------------------------------------------------------------
-- 3) Soundness relativ zum Zeit-Slice
----------------------------------------------------------------------

soundnessOnSlice :
  (G : DriftGraph) (t : ℕ) →
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  rank3? (diffs ptsZ) ≡ true → HasGoodTriple (diffs ptsZ)
soundnessOnSlice G t pr =
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  soundness (diffs ptsZ) pr
