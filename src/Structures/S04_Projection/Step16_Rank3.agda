{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 16 ▸ Rank-3 detection on time-slices (builds on Step 15)
--  * consumes historyAt / Embed3Nat from Step 15 (FoldMap)
--  * computes diffs, determinant over ℤ, boolean checker + completeness
----------------------------------------------------------------------

module Structures.S04_Projection.Step16_Rank3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_) 
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)

-- Project Bool (avoid std Data.Bool to keep one Bool in scope)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool; true; false; not)

-- Graph + FoldMap pipeline
open import Structures.S03_ProcessGraphs.Step10_DriftGraph using (DriftGraph)
open import Structures.S04_Projection.Step15_FoldMap using (historyAt ; Tripleℕ ; Embed3Nat)

----------------------------------------------------------------------
-- ℤ (as difference of two ℕ) + arithmetic
----------------------------------------------------------------------

record ℤ : Set where
  constructor z
  field pos neg : ℕ
open ℤ

infixl 7 _∗ℤ_
infixl 6 _+ℤ_ _−ℤ_

toℤ : ℕ → ℤ
toℤ n = z n 0

negℤ : ℤ → ℤ
negℤ (z p n) = z n p

_+ℤ_ : ℤ → ℤ → ℤ
z a b +ℤ z c d = z (a + c) (b + d)

_−ℤ_ : ℤ → ℤ → ℤ
x −ℤ y = x +ℤ negℤ y

-- (a−b)(c−d) = (ac+bd) − (ad+bc)
_∗ℤ_ : ℤ → ℤ → ℤ
z a b ∗ℤ z c d = z (a * c + b * d) (a * d + b * c)

-- boolean equality on ℕ (local, only for isZeroℤ)
_==_ : ℕ → ℕ → Bool
0       == 0        = true
0       == suc _    = false
suc _   == 0        = false
suc m   == suc n    = m == n

isZeroℤ : ℤ → Bool
isZeroℤ (z p n) = p == n

nonZeroℤ : ℤ → Bool
nonZeroℤ x = not (isZeroℤ x)

----------------------------------------------------------------------
-- ℤ³ + determinant
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
  let a = x r₁ ; b = y r₁ ; c = z₃ r₁
      d = x r₂ ; e = y r₂ ; f = z₃ r₂
      g = x r₃ ; h = y r₃ ; i = z₃ r₃
      ei = e ∗ℤ i ; fh = f ∗ℤ h
      di = d ∗ℤ i ; fg = f ∗ℤ g
      dh = d ∗ℤ h ; eg = e ∗ℤ g
      t₁ = a ∗ℤ (ei −ℤ fh)
      t₂ = b ∗ℤ (di −ℤ fg)
      t₃ = c ∗ℤ (dh −ℤ eg)
  in  (t₁ −ℤ t₂) +ℤ t₃

----------------------------------------------------------------------
-- Convert Step‑15 points (ℕ³) to ℤ³
----------------------------------------------------------------------

toZ3 : Tripleℕ → ℤ³
toZ3 t = mk3 (toℤ (Tripleℕ.x t)) (toℤ (Tripleℕ.y t)) (toℤ (Tripleℕ.z t))

----------------------------------------------------------------------
-- Diffs, witness search and boolean checker
----------------------------------------------------------------------

diffs : List ℤ³ → List ℤ³
diffs []             = []
diffs (_ ∷ [])       = []
diffs (p ∷ q ∷ rest) = q minus3 p ∷ diffs (q ∷ rest)

record GoodTriple : Set where
  constructor pack
  field a b c : ℤ³
        rest  : List ℤ³

rank3Witness : List ℤ³ → Maybe GoodTriple
rank3Witness (u ∷ v ∷ w ∷ rs) with nonZeroℤ (det3 u v w)
... | true  = just (pack u v w rs)
... | false = rank3Witness (v ∷ w ∷ rs)
rank3Witness _ = nothing

isJust : ∀ {a} {A : Set a} → Maybe A → Bool
isJust nothing  = false
isJust (just _) = true

rank3? : List ℤ³ → Bool
rank3? xs = isJust (rank3Witness xs)

----------------------------------------------------------------------
-- Public API: Rank‑3 on a time slice (via Step‑15)
----------------------------------------------------------------------

rank3At : DriftGraph → ℕ → Bool
rank3At G t =
  let ptsZ = map toZ3 (Embed3Nat (historyAt G t))
  in  rank3? (diffs ptsZ)

----------------------------------------------------------------------
-- Specification & completeness
----------------------------------------------------------------------

data HasGoodTriple : List ℤ³ → Set where
  here  : ∀ {u v w rs}
        → nonZeroℤ (det3 u v w) ≡ true
        → HasGoodTriple (u ∷ v ∷ w ∷ rs)
  there : ∀ {x xs} → HasGoodTriple xs → HasGoodTriple (x ∷ xs)

completeness : ∀ xs → HasGoodTriple xs → rank3? xs ≡ true
completeness []                 ()
completeness (_ ∷ [])          (there ())
completeness (_ ∷ _ ∷ [])      (there (there ()))
completeness (u ∷ v ∷ w ∷ rs)  (here h) rewrite h = refl
completeness (u ∷ v ∷ w ∷ rs)  (there p)
  with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = completeness (v ∷ w ∷ rs) p

completenessOnSlice :
  (G : DriftGraph) (t : ℕ)
  → let ptsZ = map toZ3 (Embed3Nat (historyAt G t))
     in HasGoodTriple (diffs ptsZ)
     → rank3At G t ≡ true
completenessOnSlice G t pr =
  let ptsZ = map toZ3 (Embed3Nat (historyAt G t))
  in  completeness (diffs ptsZ) pr
