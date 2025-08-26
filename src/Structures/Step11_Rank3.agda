{-# OPTIONS --safe #-}

module Structures.Step11_Rank3 where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; map)
open import Data.Vec  using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

-- Wir benutzen dein Dist aus Step2
open import Structures.Step2_VectorOperations using (Dist)

------------------------------------------------------------------------
-- Grund-Utilities: popcount, AND-Zähler, Masken
------------------------------------------------------------------------

-- popcount: wie viele 'true' in einer Distinktion
popcount : ∀ {n} → Dist n → ℕ
popcount {zero}  []       = zero
popcount {suc n} (b ∷ bs) = (if b then suc zero else zero) + popcount bs
  where
    if : ∀ {A : Set} → Bool → A → A → A
    if true  x _ = x
    if false _ y = y

-- Anzahl der Positionen, an denen beide true sind
andCount : ∀ {n} → Dist n → Dist n → ℕ
andCount {zero}  []       []       = zero
andCount {suc n} (a ∷ as) (b ∷ bs) =
  (if a ∧ b then suc zero else zero) + andCount as bs
  where
    if : ∀ {A : Set} → Bool → A → A → A
    if true  x _ = x
    if false _ y = y

-- einfache Masken, um drei unabhängige Modi zu definieren
flip : Bool → Bool
flip true  = false
flip false = true

altMask : ∀ {n} → Bool → Vec Bool n
altMask {zero}  b = []
altMask {suc n} b = b ∷ altMask {n} (flip b)

mask1 : ∀ {n} → Vec Bool n
mask1 {n} = replicate true
  where
    replicate : ∀ {A : Set}{n : ℕ} → A → Vec A n
    replicate {zero}  a = []
    replicate {suc n} a = a ∷ replicate a

mask2 : ∀ {n} → Vec Bool n
mask2 {n} = altMask true                 -- T F T F ...

-- TT  FF  TT  FF ... → periodisch 2, aber konstruktiv als Zähler variiert
mask3' : ∀ {n} → Bool → ℕ → Vec Bool n
mask3' {zero}  b k       = []
mask3' {suc n} b zero    = mask3' {suc n} (flip b) (suc (suc zero))
mask3' {suc n} b (suc k) = b ∷ mask3' {n} b k

mask3 : ∀ {n} → Vec Bool n
mask3 {n} = mask3' {n} true (suc (suc zero))

mode₁ mode₂ mode₃ : ∀ {n} → Dist n → ℕ
mode₁ {n} d = andCount d (mask1 {n})
mode₂ {n} d = andCount d (mask2 {n})
mode₃ {n} d = andCount d (mask3 {n})

------------------------------------------------------------------------
-- ℤ als (pos,neg) – rein konstruktiv; ℤ³ & Determinante
------------------------------------------------------------------------

record ℤ : Set where constructor z; field pos neg : ℕ
open ℤ public

zeroℤ : ℤ
zeroℤ = z zero zero

toℤ : ℕ → ℤ
toℤ n = z n zero

negℤ : ℤ → ℤ
negℤ (z p n) = z n p

_+ℤ_ : ℤ → ℤ → ℤ
z a b +ℤ z c d = z (a + c) (b + d)

_−ℤ_ : ℤ → ℤ → ℤ
x −ℤ y = x +ℤ negℤ y

_∗ℤ_ : ℤ → ℤ → ℤ
-- (a-b)*(c-d) = (ac+bd) - (ad+bc)
z a b ∗ℤ z c d = z (a * c + b * d) (a * d + b * c)
  where
    _*_ : ℕ → ℕ → ℕ
    zero  * n = zero
    suc m * n = n + (m * n)

nonZeroℤ : ℤ → Bool
nonZeroℤ (z zero zero) = false
nonZeroℤ _             = true

record ℤ³ : Set where
  constructor mk3
  field x y z₃ : ℤ
open ℤ³ public

_minus3_ : ℤ³ → ℤ³ → ℤ³
mk3 a b c -3 mk3 d e f = mk3 (a −ℤ d) (b −ℤ e) (c −ℤ f)

det3 : ℤ³ → ℤ³ → ℤ³ → ℤ
det3 r1 r2 r3 =
  let a = x r1 ; b = y r1 ; c = z₃ r1
      d = x r2 ; e = y r2 ; f = z₃ r2
      g = x r3 ; h = y r3 ; i = z₃ r3
  in  (a ∗ℤ (e ∗ℤ i −ℤ f ∗ℤ h))
    −ℤ (b ∗ℤ (d ∗ℤ i −ℤ f ∗ℤ g))
    +ℤ (c ∗ℤ (d ∗ℤ h −ℤ e ∗ℤ g))

------------------------------------------------------------------------
-- FoldMap: History → ℤ³, Differenzen, Rang-3-Check
------------------------------------------------------------------------

scanSum : ℕ → List ℕ → List ℕ
scanSum acc []       = []
scanSum acc (n ∷ ns) =
  let acc' = acc + n in acc' ∷ scanSum acc' ns

FoldMap : ∀ {n} → List (Dist n) → List ℤ³
FoldMap {n} hist =
  let s1 = scanSum 0 (map (mode₁ {n}) hist)
      s2 = scanSum 0 (map (mode₂ {n}) hist)
      s3 = scanSum 0 (map (mode₃ {n}) hist)
      fS = scanSum 0 (map (popcount {n}) hist)
      mul : ℕ → ℕ → ℤ
      mul a b = toℤ (a * b)
      point : ℕ → ℕ → ℕ → ℕ → ℤ³
      point a b c f = mk3 (mul a f) (mul b f) (mul c f)
  in  zip4With point s1 s2 s3 fS
  where
    zip4With : ∀ {A B C D E} → (A → B → C → D → E)
            → List A → List B → List C → List D → List E
    zip4With f []         []         []         []         = []
    zip4With f (a ∷ as)   (b ∷ bs)   (c ∷ cs)   (d ∷ ds)   =
      f a b c d ∷ zip4With f as bs cs ds

diffs : List ℤ³ → List ℤ³
diffs []                = []
diffs (_ ∷ [])          = []
diffs (p ∷ q ∷ rest)    = (q minus3 p) ∷ diffs (q ∷ rest)

rank3? : List ℤ³ → Bool
rank3? pts = go (diffs pts)
  where
    go : List ℤ³ → Bool
    go []                   = false
    go (_ ∷ [])             = false
    go (_ ∷ _ ∷ [])         = false
    go (a ∷ b ∷ c ∷ [])     = nonZeroℤ (det3 a b c)
    go (_ ∷ rest)           = go rest
