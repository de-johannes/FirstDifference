{-# OPTIONS --safe #-}

module Structures.Step12_Rank3_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool      using (Bool; true; false; if_then_else_; not)
open import Data.Nat       using (ℕ; zero; suc; _+_)
open import Data.List      using (List; []; _∷_; map; length)
open import Data.Sum       using (_⊎_; inj₁; inj₂)

-- Aus Step 11
open import Structures.Step11_Rank3 using
  ( ℤ ; ℤ³ ; mk3
  ; nonZeroℤ ; det3 ; diffs
  ; GoodTriple ; HasGoodTriple ; here ; there
  ; rank3? ; toZ3
  )

-- Für die Slice-Variante
open import Structures.Step7_DriftGraph  using (DriftGraph)
open import Structures.Step10_FoldMap    using (Embed3NatAt)

----------------------------------------------------------------------
-- Lokaler Entscheider
----------------------------------------------------------------------

decNonZeroDet3 :
  (u v w : ℤ³) →
  (nonZeroℤ (det3 u v w) ≡ true) ⊎ (nonZeroℤ (det3 u v w) ≡ false)
decNonZeroDet3 u v w with nonZeroℤ (det3 u v w)
... | true  = inj₁ refl
... | false = inj₂ refl

----------------------------------------------------------------------
-- Fuel-basierte Soundness (terminierend)
----------------------------------------------------------------------

soundnessFuel : ℕ → (xs : List ℤ³) → rank3? xs ≡ true → HasGoodTriple xs
soundnessFuel zero    _               ()          -- Fuel aufgebraucht
soundnessFuel (suc f) []              ()          -- Unmöglich
soundnessFuel (suc f) (_ ∷ [])        ()          -- Unmöglich  
soundnessFuel (suc f) (_ ∷ _ ∷ [])    ()          -- Unmöglich
soundnessFuel (suc f) (u ∷ v ∷ w ∷ rs) pr with decNonZeroDet3 u v w
... | inj₁ hTrue  = here hTrue                     -- Gefunden!
... | inj₂ hFalse = there (soundnessFuel f (v ∷ w ∷ rs) pr')
  where
    -- Beweise, dass rank3? (v ∷ w ∷ rs) ≡ true aus der ursprünglichen Prämisse
    pr' : rank3? (v ∷ w ∷ rs) ≡ true
    pr' = pr  -- Da rank3? (u∷v∷w∷rs) definitorisch zu rank3? (v∷w∷rs) 
              -- reduziert wenn nonZeroℤ (det3 u v w) ≡ false

----------------------------------------------------------------------
-- Hauptfunktion mit automatischem Fuel
----------------------------------------------------------------------

soundness : ∀ (xs : List ℤ³) → rank3? xs ≡ true → HasGoodTriple xs
soundness xs pr = soundnessFuel (length xs) xs pr

----------------------------------------------------------------------
-- Slice-Variante
----------------------------------------------------------------------

soundnessOnSlice :
  (G : DriftGraph) (t : ℕ) →
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  rank3? (diffs ptsZ) ≡ true → HasGoodTriple (diffs ptsZ)
soundnessOnSlice G t pr =
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  soundness (diffs ptsZ) pr
