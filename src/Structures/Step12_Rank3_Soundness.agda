{-# OPTIONS --safe #-}

module Structures.Step12_Rank3_Soundness where

open import Agda.Primitive using (Level)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

-- Only needed if you later add history corollaries.
open import Structures.Step2_VectorOperations using (Dist)

-- We rely solely on Step 11’s public surface.
open import Structures.Step11_Rank3 public using
  ( ℤ³
  ; det3
  ; nonZeroℤ
  ; Maybe ; just ; nothing ; isJust ; rank3Witness
  ; HasGoodTriple ; here ; there
  ; decNonZeroDet3
  )

------------------------------------------------------------------------
-- Small β-lemma for 'if false …'
------------------------------------------------------------------------

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

------------------------------------------------------------------------
-- Unfolding lemma for the program (directly from Step 11's def)
------------------------------------------------------------------------

isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
    ≡ (if nonZeroℤ (det3 u v w)
         then true
         else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

------------------------------------------------------------------------
-- Extract the tail in the 'false' branch
------------------------------------------------------------------------

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
-- No 'with' in the recursive theorem: eliminate the decision explicitly
------------------------------------------------------------------------

-- Generic eliminator for a two-way decision (to avoid 'with'-lifting):
dec-elim : ∀ {A B C : Set} → (A ⊎ B) → (A → C) → (B → C) → C
dec-elim (inj₁ a) f g = f a
dec-elim (inj₂ b) f g = g b

-- Main theorem: Soundness for the window scan (structural recursion on xs).
witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
-- Lengths < 3: impossible (by rank3Witness definition)
witnessSound []          ()
witnessSound (_ ∷ [])    ()
witnessSound (_ ∷ _ ∷ []) ()

-- Length ≥ 3
witnessSound (u ∷ v ∷ w ∷ rs) pr =
  dec-elim (decNonZeroDet3 u v w)
    (λ eqTrue  → here  {u = u} {v = v} {w = w} {rs = rs} eqTrue)
    (λ eqFalse → there (witnessSound (v ∷ w ∷ rs) (tailFromFalse eqFalse pr)))
