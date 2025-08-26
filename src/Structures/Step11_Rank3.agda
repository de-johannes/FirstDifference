{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 11 ▸ Rank-3 detection with constructive witnesses
--            • integers ℤ and triples ℤ³
--            • determinant det3 over ℤ (no floating-point)
--            • sliding-window search over diffs (any window)
--            • predicate HasGoodTriple and completeness proof
----------------------------------------------------------------------

module Structures.Step11_Rank3 where

----------------------------------------------------------------------
-- 0 · Imports
----------------------------------------------------------------------

open import Data.Bool      using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat       using (ℕ; zero; suc; _+_; _*_)
open import Data.List      using (List; []; _∷_; map)
open import Data.Vec       using (Vec; []; _∷_)      -- masks built explicitly
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

-- alternating mask  T F T F …
altMask : ∀{n} → Bool → Vec Bool n
altMask {zero}  _ = []
altMask {suc n} b = b ∷ altMask {n} (not b)

-- mode-1: all true
mask₁ : ∀{n} → Vec Bool n
mask₁ {zero}  = []
mask₁ {suc n} = true ∷ mask₁ {n}

-- mode-2: T F T F …
mask₂ : ∀{n} → Vec Bool n
mask₂ {n} = altMask true

-- mode-3: T T F F T T F F …
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
open ℤ   -- NOTE: not public (avoid clashing `neg` with Step 2)

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

_∗ℤ_ : ℤ → ℤ → ℤ            -- (a−b)(c−d) = (ac+bd) − (ad+bc)
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
-- 5 · Differences (discrete tangents) from FoldMap
----------------------------------------------------------------------

diffs : List ℤ³ → List ℤ³
diffs []              = []
diffs (_ ∷ [])        = []
diffs (p ∷ q ∷ rest)  = q minus3 p ∷ diffs (q ∷ rest)

----------------------------------------------------------------------
-- 6 · Inspect idiom for capturing definitional equality as a proof
----------------------------------------------------------------------

-- A tiny "inspect" utility: captures the value of an expression together
-- with a propositional equality to the original expression.
data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} (x : A) → Inspect x
inspect x = it x refl

----------------------------------------------------------------------
-- 7 · Sliding-window checker + constructive witnesses
----------------------------------------------------------------------

-- A compact witness that some consecutive triple is good (det ≠ 0).
record GoodTriple : Set where
  constructor pack
  field
    a b c  : ℤ³
    rest   : List ℤ³
    det-ok : nonZeroℤ (det3 a b c) ≡ true

-- A minimal Maybe (to avoid extra imports)
data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

isJust : ∀{A} → Maybe A → Bool
isJust {A} nothing  = false
isJust {A} (just _) = true

-- Termination-safe: make the recursive call only in the 'else' branch.
-- We use 'inspect' only in the 'then' branch to harvest the equality proof.
rank3Witness : List ℤ³ → Maybe GoodTriple
rank3Witness (u ∷ v ∷ w ∷ rs) =
  let b = nonZeroℤ (det3 u v w) in
  if b then
    case inspect b of λ where
      (it .true refl) → just (pack u v w rs refl)
  else
    rank3Witness (v ∷ w ∷ rs)
rank3Witness _ = nothing

-- Boolean decision: does some window pass det ≠ 0?
rank3? : List ℤ³ → Bool
rank3? xs = isJust (rank3Witness xs)

-- Public checker specialized to histories (renamed to avoid clashes).
rank3OnHistoryBool : ∀{n} → List (Dist n) → Bool
rank3OnHistoryBool {n} hist = rank3? (diffs (FoldMap {n} hist))

----------------------------------------------------------------------
-- 8 · Logical predicate and completeness proof
----------------------------------------------------------------------

-- Inductive predicate: “there exists a good consecutive triple”.
data HasGoodTriple : List ℤ³ → Set where
  here  : ∀ {u v w rs}
        → nonZeroℤ (det3 u v w) ≡ true
        → HasGoodTriple (u ∷ v ∷ w ∷ rs)
  there : ∀ {x xs}
        → HasGoodTriple xs
        → HasGoodTriple (x ∷ xs)

-- Completeness: if the predicate holds, the Boolean checker is true.
completeness : ∀ l → HasGoodTriple l → rank3? l ≡ true
-- impossible cases (lists shorter than 3 cannot satisfy HasGoodTriple)
completeness []        ()
completeness (_ ∷ [])  ()
completeness (_ ∷ _ ∷ []) ()
-- main cases
completeness (u ∷ v ∷ w ∷ rs) (here h) rewrite h = refl
completeness (u ∷ v ∷ w ∷ rs) (there p) with inspect (nonZeroℤ (det3 u v w))
... | it true  _  = refl
... | it false _  = completeness (v ∷ w ∷ rs) p

-- Specialized to histories:
completenessOnHistory :
  ∀ {n} (hist : List (Dist n)) →
  HasGoodTriple (diffs (FoldMap {n} hist)) → rank3OnHistoryBool hist ≡ true
completenessOnHistory {n} hist pr = completeness (diffs (FoldMap {n} hist)) pr
