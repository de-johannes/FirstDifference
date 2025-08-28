{-# OPTIONS --safe #-}

module Structures.Step12_Rank3_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Data.Bool      using (Bool; true; false; if_then_else_; not)
open import Data.Nat       using (ℕ; zero; suc; _+_)
open import Data.List      using (List; []; _∷_; map; length)
open import Data.Sum       using (_⊎_; inj₁; inj₂)
open import Data.Maybe     using (Maybe; just; nothing)
open import Function       using (_∘_)

-- Aus Step 11
open import Structures.Step11_Rank3 using
  ( ℤ ; ℤ³ ; mk3 ; nonZeroℤ ; det3 ; diffs
  ; GoodTriple ; HasGoodTriple ; here ; there
  ; rank3? ; rank3Witness ; toZ3
  )

-- Für Slice-Variante  
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
-- Schlüssellemma: rank3? reduziert bei false-Determinante
----------------------------------------------------------------------

rank3?-reduction : ∀ (u v w : ℤ³) (rs : List ℤ³) →
                   nonZeroℤ (det3 u v w) ≡ false →
                   rank3? (u ∷ v ∷ w ∷ rs) ≡ rank3? (v ∷ w ∷ rs)
rank3?-reduction u v w rs hFalse = 
  -- rank3? ist isJust ∘ rank3Witness
  -- rank3Witness (u∷v∷w∷rs) = if nonZeroℤ(det3 u v w) then ... else rank3Witness (v∷w∷rs)
  -- Also bei hFalse: rank3Witness (u∷v∷w∷rs) ≡ rank3Witness (v∷w∷rs)
  cong isJust (rank3Witness-reduction u v w rs hFalse)
  where
    isJust : ∀ {A : Set} → Maybe A → Bool
    isJust nothing = false
    isJust (just _) = true
    
    rank3Witness-reduction : ∀ (u v w : ℤ³) (rs : List ℤ³) →
                             nonZeroℤ (det3 u v w) ≡ false →
                             rank3Witness (u ∷ v ∷ w ∷ rs) ≡ rank3Witness (v ∷ w ∷ rs)
    rank3Witness-reduction u v w rs hFalse with nonZeroℤ (det3 u v w)
    ... | true  rewrite hFalse = refl  -- Widerspruch, aber Agda löst es auf
    ... | false = refl                 -- Direkte Gleichheit per Definition

----------------------------------------------------------------------
-- Soundness mit explizitem Reduktionsbeweis
----------------------------------------------------------------------

soundness : ∀ (xs : List ℤ³) → rank3? xs ≡ true → HasGoodTriple xs
soundness []              ()
soundness (_ ∷ [])        ()  
soundness (_ ∷ _ ∷ [])    ()
soundness (u ∷ v ∷ w ∷ rs) pr with decNonZeroDet3 u v w
... | inj₁ hTrue  = here hTrue
... | inj₂ hFalse = there (soundness (v ∷ w ∷ rs) pr')
  where
    pr' : rank3? (v ∷ w ∷ rs) ≡ true  
    pr' = trans (rank3?-reduction u v w rs hFalse) pr

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
