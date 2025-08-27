{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness via Witness and Length Measure (safe)
--  Strategy: Separate computation (rank3Witness) and proof.
--  Statement proved here:
--     ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
--  Technique: Recursion on an explicit length measure so termination
--  is obvious to Agda's checker under --safe.
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat       using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

-- Only needed later if you add corollaries on histories.
open import Structures.Step2_VectorOperations using (Dist)

-- Import exactly what we rely on from Step 11
open import Structures.Step11_Rank3 public using
  ( ℤ³
  ; det3
  ; nonZeroℤ

  ; Maybe
  ; just
  ; nothing
  ; isJust
  ; rank3Witness

  ; HasGoodTriple
  ; here
  ; there
  ; pack
  )

----------------------------------------------------------------------
-- Inspect utility (captures definitional equality of a computed term)
----------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} → (x : A) → Inspect x
inspect x = it x refl

----------------------------------------------------------------------
-- Small β-lemma for 'if false then ... else ...'
----------------------------------------------------------------------

if-false-β : ∀ {A : Set} (x y : A) → (if false then x else y) ≡ y
if-false-β x y = refl

----------------------------------------------------------------------
-- Behaviour of isJust ∘ rank3Witness on lists with ≥ 3 elements
-- Non-recursive unfolding: matches the definition in Step 11.
----------------------------------------------------------------------

isJust-cons :
  ∀ (u v w : ℤ³) (rs : List ℤ³) →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs))
  ≡ (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs)))
isJust-cons u v w rs with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = refl

----------------------------------------------------------------------
-- From a failed head test we extract the tail obligation
----------------------------------------------------------------------

tailFromFalse :
  ∀ {u v w rs} →
  nonZeroℤ (det3 u v w) ≡ false →
  isJust (rank3Witness (u ∷ v ∷ w ∷ rs)) ≡ true →
  isJust (rank3Witness (v ∷ w ∷ rs)) ≡ true
tailFromFalse {u} {v} {w} {rs} eqFalse pr =
  let
    -- Replace witness by its head-unfolding and transport equality
    pr-cond :
      (if nonZeroℤ (det3 u v w) then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-cond = trans (sym (isJust-cons u v w rs)) pr

    -- Substitute false for the condition
    pr-false :
      (if false then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true
    pr-false =
      subst (λ b → (if b then true else isJust (rank3Witness (v ∷ w ∷ rs))) ≡ true)
            eqFalse
            pr-cond
  in
    -- Eliminate the if with 'false' and conclude the tail is true
    trans (sym (if-false-β true (isJust (rank3Witness (v ∷ w ∷ rs))))) pr-false

----------------------------------------------------------------------
-- Length measure for lists of ℤ³ and an indexed soundness proof.
-- The length index makes the recursive call strictly smaller.
----------------------------------------------------------------------

len3 : List ℤ³ → ℕ
len3 []       = zero
len3 (_ ∷ xs) = suc (len3 xs)

-- Main indexed proof: recursion on the length index.
witnessSoundLen :
  ∀ n (xs : List ℤ³) →
  len3 xs ≡ n →
  isJust (rank3Witness xs) ≡ true →
  HasGoodTriple xs

-- Length 0: impossible (rank3Witness = nothing ⇒ isJust = false)
witnessSoundLen .zero [] refl ()

-- Length 1: impossible
witnessSoundLen .(suc zero) (_ ∷ []) refl ()

-- Length 2: impossible
witnessSoundLen .(suc (suc zero)) (_ ∷ _ ∷ []) refl ()

-- Length ≥ 3: bind 'n' (no dot), head test; success ⇒ 'here', else recurse on tail
witnessSoundLen (suc (suc (suc n))) (u ∷ v ∷ w ∷ rs) refl pr
  with inspect (nonZeroℤ (det3 u v w))
... | it true  eqTrue  =
      here {u = u} {v = v} {w = w} {rs = rs} eqTrue
... | it false eqFalse =
      there (witnessSoundLen (suc (suc n)) (v ∷ w ∷ rs) refl (tailFromFalse eqFalse pr))

----------------------------------------------------------------------
-- Wrapper with the actual statement (no explicit length in the type)
----------------------------------------------------------------------

witnessSound : ∀ xs → isJust (rank3Witness xs) ≡ true → HasGoodTriple xs
witnessSound xs = witnessSoundLen (len3 xs) xs refl
