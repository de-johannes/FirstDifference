{-# OPTIONS --safe              #-}

module Structures.Step11_Rank3 where

------------------------------------------------------------------------
-- Import-Organisation
------------------------------------------------------------------------

open import Data.Bool                    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat                     using (ℕ; zero; suc; _+_; _*_)
open import Data.List                    using (List; []; _∷_; map)
open import Data.Product                 using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Vektoren:  Vec (sicher) statt List + Länge
open import Data.Vec                     using (Vec; []; _∷_; replicate)

-- Dist aus Step2 (bleibt wie gehabt)
open import Structures.Step2_VectorOperations using (Dist)

------------------------------------------------------------------------
-- 1. Kleine Bool-Helfer
------------------------------------------------------------------------

not : Bool → Bool
not true  = false
not false = true

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

------------------------------------------------------------------------
-- 2. Popcount, AND-Counter & Masken
------------------------------------------------------------------------

popcount : ∀{n} → Dist n → ℕ
popcount {zero}  []       = zero
popcount {suc _} (b ∷ bs) = (if b then 1 else 0) + popcount bs

andCount : ∀{n} → Dist n → Dist n → ℕ
andCount {zero}  []       []       = zero
andCount {suc _} (a ∷ as) (b ∷ bs) =
  (if a ∧ b then 1 else 0) + andCount as bs

-- ► Masken: generisch & tail-rekursiv

altMask : ∀{n} → Bool → Vec Bool n
altMask {zero}  _ = []
altMask {suc n} b = b ∷ altMask {n} (not b)

mask₁ : ∀{n} → Vec Bool n
mask₁ {n} = replicate true

mask₂ : ∀{n} → Vec Bool n
mask₂ {n} = altMask true          -- T F T F …

mask₃ : ∀{n} → Vec Bool n
mask₃ {zero}  = []
mask₃ {suc n} = true ∷ true ∷ altMask {n} false   -- TT FF TT …

mode₁ mode₂ mode₃ : ∀{n} → Dist n → ℕ
mode₁ {n} d = andCount d (mask₁ {n})
mode₂ {n} d = andCount d (mask₂ {n})
mode₃ {n} d = andCount d (mask₃ {n})

------------------------------------------------------------------------
-- 3. ℤ als (pos, neg)  & Basis-Arithmetik
------------------------------------------------------------------------

record ℤ : Set where
  constructor z
  field pos neg : ℕ
open ℤ public

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

_∗ℤ_ : ℤ → ℤ → ℤ        --  (a−b)(c−d) = (ac+bd) − (ad+bc)
z a b ∗ℤ z c d =
  z (a * c + b * d)
    (a * d + b * c)

isZeroℤ : ℤ → Bool
isZeroℤ (z p n) = eqℕ p n

nonZeroℤ : ℤ → Bool
nonZeroℤ = not ∘ isZeroℤ

------------------------------------------------------------------------
-- 4. ℤ³ & Determinante 3×3
------------------------------------------------------------------------

record ℤ³ : Set where
  constructor mk3
  field x y z₃ : ℤ
open ℤ³ public

_minus3_ : ℤ³ → ℤ³ → ℤ³
mk3 a b c minus3 mk3 d e f = mk3 (a −ℤ d) (b −ℤ e) (c −ℤ f)

det3 : ℤ³ → ℤ³ → ℤ³ → ℤ
det3 r₁ r₂ r₃ =
  let open ℤ³ in
      a = x r₁ ; b = y r₁ ; c = z₃ r₁
      d = x r₂ ; e = y r₂ ; f = z₃ r₂
      g = x r₃ ; h = y r₃ ; i = z₃ r₃
      t₁ = a ∗ℤ (e ∗ℤ i −ℤ f ∗ℤ h)
      t₂ = b ∗ℤ (d ∗ℤ i −ℤ f ∗ℤ g)
      t₃ = c ∗ℤ (d ∗ℤ h −ℤ e ∗ℤ g)
  in  (t₁ −ℤ t₂) +ℤ t₃

------------------------------------------------------------------------
-- 5. FoldMap → ℤ³-Historie, Differenzen, Rang-3-Check
------------------------------------------------------------------------

-- Summenlauf (exclusive scan)
scanSum : ℕ → List ℕ → List ℕ
scanSum _ []       = []
scanSum acc (n ∷ ns)
  with let acc′ = acc + n
  ... | acc′ = acc′ ∷ scanSum acc′ ns

-- Faltet Dist-Historie in Punkte ℤ³
FoldMap : ∀{n} → List (Dist n) → List ℤ³
FoldMap {n} hist =
  let s₁ = scanSum 0 (map (mode₁ {n}) hist)
      s₂ = scanSum 0 (map (mode₂ {n}) hist)
      s₃ = scanSum 0 (map (mode₃ {n}) hist)
      fs = scanSum 0 (map (popcount {n}) hist)

      mul : ℕ → ℕ → ℤ
      mul a b = toℤ (a * b)

      point : ℕ → ℕ → ℕ → ℕ → ℤ³
      point a b c f = mk3 (mul a f) (mul b f) (mul c f)

      -- Hilfs-Zip über vier Listen
      zip⁴ : ∀{A B C D E} →
             (A → B → C → D → E) →
             List A → List B → List C → List D → List E
      zip⁴ _ []         []         []         []         = []
      zip⁴ f (a ∷ as)   (b ∷ bs)   (c ∷ cs)   (d ∷ ds)   =
        f a b c d ∷ zip⁴ f as bs cs ds
  in  zip⁴ point s₁ s₂ s₃ fs

-- Differenzen benachbarter Punkte
diffs : List ℤ³ → List ℤ³
diffs []              = []
diffs (_ ∷ [])        = []
diffs (p ∷ q ∷ rest)  = q minus3 p ∷ diffs (q ∷ rest)

-- Rang-3-Determinanten-Test auf irgendeinem Tripel
rank3? : List ℤ³ → Bool
rank3? pts = go (diffs pts)
  where
    go : List ℤ³ → Bool
    go (a ∷ b ∷ c ∷ []) = nonZeroℤ (det3 a b c)
    go (_ ∷ rest)       = go rest
    go _                = false          -- < 3 Vektoren ⇒ kein Rang 3
