{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 11 ▸ Rank-3 detection in the Drift-Graph fold-map
----------------------------------------------------------------------

module Structures.Step11_Rank3 where

----------------------------------------------------------------------
-- 0 · Imports
----------------------------------------------------------------------

open import Data.Bool      using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat       using (ℕ; zero; suc; _+_; _*_)
open import Data.List      using (List; []; _∷_; map)
open import Data.Vec       using (Vec; []; _∷_)         -- no replicate here
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Primitive using (Level; lzero; _⊔_)

open import Structures.Step2_VectorOperations using (Dist)
open import Structures.Step10_FoldMap         using (FoldMap)

----------------------------------------------------------------------
-- 1 · Tiny helpers
----------------------------------------------------------------------

not : Bool → Bool
not true  = false
not false = true

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

----------------------------------------------------------------------
-- 2 · Pop-count, AND-count, masks
----------------------------------------------------------------------

popcount : ∀{n} → Dist n → ℕ
popcount {zero}  []       = zero
popcount {suc _} (b ∷ xs) = (if b then 1 else 0) + popcount xs

andCount : ∀{n} → Dist n → Dist n → ℕ
andCount {zero}  []       []       = zero
andCount {suc _} (a ∷ as) (b ∷ bs) =
  (if a ∧ b then 1 else 0) + andCount as bs

-- infinite alternation  T F T F …
altMask : ∀{n} → Bool → Vec Bool n
altMask {zero}  _ = []
altMask {suc n} b = b ∷ altMask {n} (not b)

-- mode-1: all true  (explicit, avoids replicate to keep things simple)
mask₁ : ∀{n} → Vec Bool n
mask₁ {zero}  = []
mask₁ {suc n} = true ∷ mask₁ {n}

-- mode-2:  T F T F …
mask₂ : ∀{n} → Vec Bool n
mask₂ {n} = altMask true

-- mode-3:  T T F F T T F F …
two : ℕ
two = suc (suc zero)

pred : ℕ → ℕ
pred zero    = zero
pred (suc k) = k

mask3Aux : ∀{n} → Bool → ℕ → Vec Bool n
mask3Aux {zero}  _ _ = []
mask3Aux {suc n} b t = b ∷ mask3Aux {n} b' t'
  where
    done? = eqℕ t zero
    b'    = if done? then not b else b
    t'    = if done? then two    else pred t

mask₃ : ∀{n} → Vec Bool n
mask₃ {n} = mask3Aux {n} true two

mode₁ mode₂ mode₃ : ∀{n} → Dist n → ℕ
mode₁ {n} d = andCount d (mask₁ {n})
mode₂ {n} d = andCount d (mask₂ {n})
mode₃ {n} d = andCount d (mask₃ {n})

----------------------------------------------------------------------
-- 3 · Integers ℤ (pos,neg) + arithmetic
----------------------------------------------------------------------

record ℤ : Set where
  constructor z
  field pos neg : ℕ
open ℤ   -- NOTE: not public, to avoid exporting `neg` and clashing with Step2

zeroℤ : ℤ
zeroℤ = z 0 0

toℤ : ℕ → ℤ
toℤ n = z n 0

negℤ : ℤ → ℤ
negℤ (z p n) = z n p

_+ℤ_ : ℤ → ℤ → ℤ
z a b +ℤ z c d = z (a + c) (b + d)

_−ℤ_ : ℤ → ℤ → ℤ
x −ℤ y = x +ℤ negℤ y

_∗ℤ_ : ℤ → ℤ → ℤ           -- (a−b)(c−d) = (ac+bd) − (ad+bc)
z a b ∗ℤ z c d =
  z (a * c + b * d)
    (a * d + b * c)

isZeroℤ : ℤ → Bool
isZeroℤ (z p n) = eqℕ p n

nonZeroℤ : ℤ → Bool
nonZeroℤ x = not (isZeroℤ x)

----------------------------------------------------------------------
-- 4 · Triples ℤ³ + 3×3 determinant
----------------------------------------------------------------------

record ℤ³ : Set where
  constructor mk3
  field x y z₃ : ℤ
open ℤ³ public

infixl 6 _minus3_

_minus3_ : ℤ³ → ℤ³ → ℤ³
mk3 a b c minus3 mk3 d e f = mk3 (a −ℤ d) (b −ℤ e) (c −ℤ f)

det3 : ℤ³ → ℤ³ → ℤ³ → ℤ
det3 r₁ r₂ r₃ =
  let a  = x r₁ ; b  = y r₁ ; c  = z₃ r₁
      d  = x r₂ ; e  = y r₂ ; f  = z₃ r₂
      g  = x r₃ ; h  = y r₃ ; i  = z₃ r₃

      ei = e ∗ℤ i ; fh = f ∗ℤ h
      di = d ∗ℤ i ; fg = f ∗ℤ g
      dh = d ∗ℤ h ; eg = e ∗ℤ g

      t₁ = a ∗ℤ (ei −ℤ fh)
      t₂ = b ∗ℤ (di −ℤ fg)
      t₃ = c ∗ℤ (dh −ℤ eg)
  in  (t₁ −ℤ t₂) +ℤ t₃

----------------------------------------------------------------------
-- 5 · Rank-3 test via sliding determinant
--     (FoldMap is imported from Step 10)
----------------------------------------------------------------------

-- Differences of consecutive points in ℤ³
diffs : List ℤ³ → List ℤ³
diffs []              = []
diffs (_ ∷ [])        = []
diffs (p ∷ q ∷ rest)  = q minus3 p ∷ diffs (q ∷ rest)

-- Checks whether some 3 successive differences are linearly independent
rank3? : List ℤ³ → Bool
rank3? pts = slide (diffs pts)
  where
    slide : List ℤ³ → Bool
    slide (a ∷ b ∷ c ∷ []) = nonZeroℤ (det3 a b c)
    slide (_ ∷ rest)       = slide rest
    slide _                = false
