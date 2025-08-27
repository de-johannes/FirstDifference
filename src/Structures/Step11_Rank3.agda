{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 11 ▸ Rank-3 detection with constructive witnesses
----------------------------------------------------------------------

module Structures.Step11_Rank3 where

----------------------------------------------------------------------
-- 0 · Imports
----------------------------------------------------------------------

open import Data.Bool      using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat       using (ℕ; zero; suc; _+_; _*_)
open import Data.List      using (List; []; _∷_; map)
open import Data.Vec       using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Primitive using (Level)

open import Structures.Step2_VectorOperations using (Dist)
open import Structures.Step10_FoldMap         using (FoldMap)

----------------------------------------------------------------------
-- 1 · Helper functions
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
-- 2 · Mode masks
----------------------------------------------------------------------

popcount : ∀ {n} → Dist n → ℕ
popcount {zero}  []       = zero
popcount {suc _} (b ∷ xs) = (if b then 1 else 0) + popcount xs

andCount : ∀ {n} → Dist n → Dist n → ℕ
andCount {zero}  []       []       = zero
andCount {suc _} (a ∷ as) (b ∷ bs) =
  (if a ∧ b then 1 else 0) + andCount as bs

altMask : ∀ {n} → Bool → Vec Bool n       -- T F T F …
altMask {zero}  _ = []
altMask {suc n} b = b ∷ altMask {n} (not b)

mask₁ : ∀ {n} → Vec Bool n                -- all true
mask₁ {zero}  = []
mask₁ {suc n} = true ∷ mask₁ {n}

mask₂ : ∀ {n} → Vec Bool n                -- alternation
mask₂ {n} = altMask true

two : ℕ
two = suc (suc zero)

pred : ℕ → ℕ
pred zero    = zero
pred (suc k) = k

mask3Aux : ∀ {n} → Bool → ℕ → Vec Bool n  -- T T F F …
mask3Aux {zero}  _ _ = []
mask3Aux {suc n} b t = b ∷ mask3Aux {n} b' t'
  where
    done? = eqℕ t zero
    b'    = if done? then not b else b
    t'    = if done? then two    else pred t

mask₃ : ∀ {n} → Vec Bool n
mask₃ {n} = mask3Aux {n} true two

mode₁ mode₂ mode₃ : ∀ {n} → Dist n → ℕ
mode₁ {n} d = andCount d (mask₁ {n})
mode₂ {n} d = andCount d (mask₂ {n})
mode₃ {n} d = andCount d (mask₃ {n})

----------------------------------------------------------------------
-- 3 · Integers ℤ
----------------------------------------------------------------------

record ℤ : Set where
  constructor z
  field pos neg : ℕ
open ℤ

infixl 7 _∗ℤ_
infixl 6 _+ℤ_ _−ℤ_

zeroℤ : ℤ
zeroℤ = z 0 0

_+ℤ_ : ℤ → ℤ → ℤ
z a b +ℤ z c d = z (a + c) (b + d)

negℤ : ℤ → ℤ
negℤ (z p n) = z n p

_−ℤ_ : ℤ → ℤ → ℤ
x −ℤ y = x +ℤ negℤ y

_∗ℤ_ : ℤ → ℤ → ℤ            -- (a−b)(c−d)
z a b ∗ℤ z c d = z (a * c + b * d) (a * d + b * c)

isZeroℤ : ℤ → Bool
isZeroℤ (z p n) = eqℕ p n

nonZeroℤ : ℤ → Bool
nonZeroℤ x = not (isZeroℤ x)

----------------------------------------------------------------------
-- 4 · Triples ℤ³  + determinant
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
-- 5 · Differences of FoldMap points
----------------------------------------------------------------------

diffs : List ℤ³ → List ℤ³
diffs []              = []
diffs (_ ∷ [])        = []
diffs (p ∷ q ∷ rs)    = q minus3 p ∷ diffs (q ∷ rs)

----------------------------------------------------------------------
-- 6 · Inspect utility
----------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A} → (x : A) → Inspect x
inspect x = it x refl

----------------------------------------------------------------------
-- 7 · Witness search & Boolean checker
----------------------------------------------------------------------

record GoodTriple : Set where
  constructor pack
  field a b c : ℤ³
        rest  : List ℤ³
        det-ok : nonZeroℤ (det3 a b c) ≡ true

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

isJust : ∀ {A} → Maybe A → Bool
isJust nothing  = false
isJust (just _) = true

-- uses inspect → explicit equality proof; recursion only in 'false' path
rank3Witness : List ℤ³ → Maybe GoodTriple
rank3Witness (u ∷ v ∷ w ∷ rs)
  with inspect (nonZeroℤ (det3 u v w))
... | it true  eq = just (pack u v w rs eq)
... | it false _  = rank3Witness (v ∷ w ∷ rs)
rank3Witness _ = nothing

rank3? : List ℤ³ → Bool
rank3? xs = isJust (rank3Witness xs)

rank3OnHistoryBool : ∀ {n} → List (Dist n) → Bool
rank3OnHistoryBool {n} h = rank3? (diffs (FoldMap {n} h))

----------------------------------------------------------------------
-- 8 · Spec predicate & completeness proof
----------------------------------------------------------------------

data HasGoodTriple : List ℤ³ → Set where
  here  : ∀ {u v w rs}
        → nonZeroℤ (det3 u v w) ≡ true
        → HasGoodTriple (u ∷ v ∷ w ∷ rs)
  there : ∀ {x xs} → HasGoodTriple xs → HasGoodTriple (x ∷ xs)

completeness : ∀ xs → HasGoodTriple xs → rank3? xs ≡ true
completeness []        ()
completeness (_ ∷ [])  ()
completeness (_ ∷ _ ∷ []) ()
completeness (u ∷ v ∷ w ∷ rs) (here h) rewrite h = refl
completeness (u ∷ v ∷ w ∷ rs) (there p)
  with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = completeness (v ∷ w ∷ rs) p

completenessOnHistory :
  ∀ {n} (hist : List (Dist n)) →
  HasGoodTriple (diffs (FoldMap {n} hist)) →
  rank3OnHistoryBool hist ≡ true
completenessOnHistory {n} h pr =
  completeness (diffs (FoldMap {n} h)) pr
