{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 17 ▸ Rank-3 Soundness (ported from old Step 12)
--  * Direction opposite to Step 16:
--      rank3? xs ≡ true  ⇒  HasGoodTriple xs
--  * plus: slice variant via Step 15/16
--  * TERMINATING by measure (list length, with ≤-proof)
----------------------------------------------------------------------

module Structures.S04_Projection.Step16_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Sum       using (_⊎_; inj₁; inj₂)
open import Data.Nat       using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List      using (List; []; _∷_; map; length)

-- Use project Bool (no std Data.Bool)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool; true; false)

-- Core Rank-3 machinery from Step 16
open import Structures.S04_Projection.Step16_Rank3 using
  ( ℤ ; ℤ³ ; mk3
  ; nonZeroℤ
  ; det3
  ; diffs
  ; GoodTriple ; HasGoodTriple ; here ; there
  ; rank3?     -- Bool checker
  ; toZ3
  ; step-when-false[] ; step-when-false∷   -- helper lemmas from Step 16
  )

-- Step 15: point cloud per time-slice
open import Structures.S03_ProcessGraphs.Step10_DriftGraph using (DriftGraph)
open import Structures.S04_Projection.Step15_FoldMap      using (historyAt ; Embed3Nat)

----------------------------------------------------------------------
-- 0) Decider for nonZero(det3 u v w) (local)
----------------------------------------------------------------------

decNonZeroDet3 :
  (u v w : ℤ³) →
  (nonZeroℤ (det3 u v w) ≡ true) ⊎ (nonZeroℤ (det3 u v w) ≡ false)
decNonZeroDet3 u v w with nonZeroℤ (det3 u v w)
... | true  = inj₁ refl
... | false = inj₂ refl

----------------------------------------------------------------------
-- 1) Window shift when det = 0  (prove equality of rank3? values)
----------------------------------------------------------------------

rank3?-step :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  nonZeroℤ (det3 u v w) ≡ false →
  rank3? (u ∷ v ∷ w ∷ rs) ≡ rank3? (v ∷ w ∷ rs)
-- split on rs to align with Step16's 'step' definition
rank3?-step u v w []      hFalse rewrite step-when-false[] u v w hFalse = refl
rank3?-step u v w (x ∷ xs) hFalse rewrite step-when-false∷ u v w x xs hFalse = refl

-- pull ≤ on tails
tail≤ : ∀ {n k} → suc n ≤ suc k → n ≤ k
tail≤ (s≤s p) = p

-- length ≤ length (reflexive) – level-polymorphic
len≤len : ∀ {a} {A : Set a} (xs : List A) → length xs ≤ length xs
len≤len []       = z≤n
len≤len (_ ∷ xs) = s≤s (len≤len xs)

----------------------------------------------------------------------
-- 2) Soundness with measure (length xs) as fuel and proof length xs ≤ k
----------------------------------------------------------------------

soundness′ : ∀ (xs : List ℤ³) (k : ℕ)
           → length xs ≤ k
           → rank3? xs ≡ true
           → HasGoodTriple xs
-- Lists < 3: impossible, since rank3? [] / [_] / [_, _] = false
soundness′ []           _ _  ()
soundness′ (_ ∷ [])     _ _  ()
soundness′ (_ ∷ _ ∷ []) _ _  ()

-- ≥ 3 points, k = 0: impossible (suc … ≤ 0 not constructible)
soundness′ (u ∷ v ∷ w ∷ rs) zero     () pr

-- ≥ 3 points, k = suc k′: normal step
soundness′ (u ∷ v ∷ w ∷ rs) (suc k) le pr with decNonZeroDet3 u v w
... | inj₁ hTrue  = here hTrue
... | inj₂ hFalse =
  let step  : rank3? (u ∷ v ∷ w ∷ rs) ≡ rank3? (v ∷ w ∷ rs)
      step  = rank3?-step u v w rs hFalse
      pr′   : rank3? (v ∷ w ∷ rs) ≡ true
      pr′   = trans (sym step) pr
      le′   : length (v ∷ w ∷ rs) ≤ k
      le′   = tail≤ le
  in  there (soundness′ (v ∷ w ∷ rs) k le′ pr′)

-- Public wrapper: choose k := length xs with reflexivity
soundness : ∀ (xs : List ℤ³) → rank3? xs ≡ true → HasGoodTriple xs
soundness xs pr = soundness′ xs (length xs) (len≤len xs) pr

----------------------------------------------------------------------
-- 3) Soundness relative to a time slice
----------------------------------------------------------------------

soundnessOnSlice :
  (G : DriftGraph) (t : ℕ) →
  let ptsZ = map toZ3 (Embed3Nat (historyAt G t))
  in  rank3? (diffs ptsZ) ≡ true → HasGoodTriple (diffs ptsZ)
soundnessOnSlice G t pr =
  let ptsZ = map toZ3 (Embed3Nat (historyAt G t))
  in  soundness (diffs ptsZ) pr
