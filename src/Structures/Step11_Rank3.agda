{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 11 ▸ Rank-3 detection, slice/time-aware (replaces old Step 11)
--            Keine Abhängigkeit von Step 10; numerische Einbettung lokal als Embed³
----------------------------------------------------------------------

module Structures.Step11_Rank3 where

----------------------------------------------------------------------
-- 0 · Imports
----------------------------------------------------------------------

open import Agda.Primitive using (Level)

open import Data.Bool      using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat       using (ℕ; zero; suc; _+_; _*_)
open import Data.List      using (List; []; _∷_; map)
open import Data.Vec       using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum.Base  using (_⊎_; inj₁; inj₂)

-- Dist (Bit-Vektor)
open import Structures.Step2_VectorOperations using (Dist)

-- Zeit/Graph/Slice (Step 9)
open import Structures.Step7_DriftGraph       using (DriftGraph)
open import Structures.Step9_SpatialStructure using (same-rank-nodes ; node-to-dist)

----------------------------------------------------------------------
-- 1 · Kleine Helfer
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
-- 2 · Mode-Masken & Zähler
----------------------------------------------------------------------

popcount : ∀ {n} → Dist n → ℕ
popcount {zero}  []       = zero
popcount {suc _} (b ∷ xs) = (if b then 1 else 0) + popcount xs

andCount : ∀ {n} → Dist n → Dist n → ℕ
andCount {zero}  []       []       = zero
andCount {suc _} (a ∷ as) (b ∷ bs) =
  (if a ∧ b then 1 else 0) + andCount as bs

-- alternating mask  T F T F …
altMask : ∀ {n} → Bool → Vec Bool n
altMask {zero}  _ = []
altMask {suc n} b = b ∷ altMask {n} (not b)

-- mode-1: alle true
mask₁ : ∀ {n} → Vec Bool n
mask₁ {zero}  = []
mask₁ {suc n} = true ∷ mask₁ {n}

-- mode-2:  T F T F …
mask₂ : ∀ {n} → Vec Bool n
mask₂ {n} = altMask true

-- mode-3:  T T F F T T F F …
two : ℕ
two = suc (suc zero)

pred : ℕ → ℕ
pred zero    = zero
pred (suc k) = k

mask3Aux : ∀ {n} → Bool → ℕ → Vec Bool n
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
-- 3 · Ganze Zahlen ℤ
----------------------------------------------------------------------

record ℤ : Set where
  constructor z
  field pos neg : ℕ
open ℤ

infixl 7 _∗ℤ_
infixl 6 _+ℤ_ _−ℤ_

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
z a b ∗ℤ z c d = z (a * c + b * d) (a * d + b * c)

isZeroℤ : ℤ → Bool
isZeroℤ (z p n) = eqℕ p n

nonZeroℤ : ℤ → Bool
nonZeroℤ x = not (isZeroℤ x)

----------------------------------------------------------------------
-- 4 · Triples ℤ³  + Determinante
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
-- 5 · Prefix-Summen, Zipper, Einbettung Embed³ (statt „lokales FoldMap³“)
----------------------------------------------------------------------

-- exclusive prefix sums
scanSum : ℕ → List ℕ → List ℕ
scanSum _   []       = []
scanSum acc (n ∷ ns) with acc + n | scanSum (acc + n) ns
... | acc′ | rest = acc′ ∷ rest

-- 4-way zipper
zip⁴ : ∀ {ℓA ℓB ℓC ℓD ℓE}
       {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {D : Set ℓD} {E : Set ℓE}
     → (A → B → C → D → E)
     → List A → List B → List C → List D → List E
zip⁴ _ []         _          _          _          = []
zip⁴ _ _          []         _          _          = []
zip⁴ _ _          _          []         _          = []
zip⁴ _ _          _          _          []         = []
zip⁴ f (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) =
  f a b c d ∷ zip⁴ f as bs cs ds

-- Embed³: History (Dist) → ℤ³ Punkte mittels drei Moden + Gewicht (popcount)
Embed³ : ∀ {n} → List (Dist n) → List ℤ³
Embed³ {n} hist =
  let s₁ = scanSum 0 (map (mode₁ {n}) hist)
      s₂ = scanSum 0 (map (mode₂ {n}) hist)
      s₃ = scanSum 0 (map (mode₃ {n}) hist)
      fs = scanSum 0 (map (popcount {n}) hist)

      mul : ℕ → ℕ → ℤ
      mul a b = toℤ (a * b)

      point : ℕ → ℕ → ℕ → ℕ → ℤ³
      point a b c f = mk3 (mul a f) (mul b f) (mul c f)
  in  zip⁴ point s₁ s₂ s₃ fs

----------------------------------------------------------------------
-- 6 · Differenzen der Punkte
----------------------------------------------------------------------

diffs : List ℤ³ → List ℤ³
diffs []           = []
diffs (_ ∷ [])     = []
diffs (p ∷ q ∷ rs) = q minus3 p ∷ diffs (q ∷ rs)

----------------------------------------------------------------------
-- 7 · Zeugen-Suche & Bool-Checker
----------------------------------------------------------------------

record GoodTriple : Set where
  constructor pack
  field a b c : ℤ³
        rest  : List ℤ³

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

isJust : ∀ {A} → Maybe A → Bool
isJust nothing  = false
isJust (just _) = true

rank3Witness : List ℤ³ → Maybe GoodTriple
rank3Witness (u ∷ v ∷ w ∷ rs) =
  if nonZeroℤ (det3 u v w)
  then just (pack u v w rs)
  else rank3Witness (v ∷ w ∷ rs)
rank3Witness _ = nothing

rank3? : List ℤ³ → Bool
rank3? xs = isJust (rank3Witness xs)

-- Öffentliche API: Rank-3 auf dem ZEIT-SLICE (Step 9)
rank3At : ∀ {n} → DriftGraph → ℕ → Bool
rank3At {n} G t =
  let hist : List (Dist n)
      hist = map (node-to-dist {n}) (same-rank-nodes G t)
  in  rank3? (diffs (Embed³ {n} hist))

abstract
  decNonZeroDet3 : ∀ (u v w : ℤ³)
                 → (nonZeroℤ (det3 u v w) ≡ true)
                 ⊎ (nonZeroℤ (det3 u v w) ≡ false)
  decNonZeroDet3 u v w with nonZeroℤ (det3 u v w)
  ... | true  = inj₁ refl
  ... | false = inj₂ refl

----------------------------------------------------------------------
-- 8 · Spezifikation & Vollständigkeit
----------------------------------------------------------------------

data HasGoodTriple : List ℤ³ → Set where
  here  : ∀ {u v w rs}
        → nonZeroℤ (det3 u v w) ≡ true
        → HasGoodTriple (u ∷ v ∷ w ∷ rs)
  there : ∀ {x xs} → HasGoodTriple xs → HasGoodTriple (x ∷ xs)

completeness : ∀ xs → HasGoodTriple xs → rank3? xs ≡ true
completeness []               ()
completeness (_ ∷ [])        (there ())
completeness (_ ∷ _ ∷ [])    (there (there ()))
completeness (u ∷ v ∷ w ∷ rs) (here h) rewrite h = refl
completeness (u ∷ v ∷ w ∷ rs) (there p)
  with nonZeroℤ (det3 u v w)
... | true  = refl
... | false = completeness (v ∷ w ∷ rs) p

-- Vollständigkeit relativ zum Zeit-Slice
completenessOnSlice :
  ∀ {n} (G : DriftGraph) (t : ℕ)
  → let hist = map (node-to-dist {n}) (same-rank-nodes G t)
     in HasGoodTriple (diffs (Embed³ {n} hist))
     → rank3At {n} G t ≡ true
completenessOnSlice {n} G t pr =
  let hist = map (node-to-dist {n}) (same-rank-nodes G t)
  in  completeness (diffs (Embed³ {n} hist)) pr
