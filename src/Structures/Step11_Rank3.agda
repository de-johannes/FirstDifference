{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 11 ▸ Rank-3 Detection on Spatial Slices (KORRIGIERT)
--  * Korrekte Standard Library Imports
--  * Nutzt Step9's SpatialSlice mit semantic time als Parameter
----------------------------------------------------------------------

module Structures.Step11_Rank3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.Nat       using (ℕ; zero; suc; _+_; _*_)
-- KORRIGIERT: Richtige Integer-Imports
open import Data.Integer   using (ℤ; +_; -[1+_])
open import Data.Integer.Base using (_+ℤ_; _-ℤ_; _*ℤ_)
open import Data.List      using (List; []; _∷_; map)
-- KORRIGIERT: Richtige Maybe-Imports
open import Data.Maybe     using (Maybe; just; nothing)
open import Data.Maybe.Base using (is-just)
-- KORRIGIERT: Product für × Typ
open import Data.Product   using (_×_; _,_)

-- KORRIGIERT: DriftGraph ist in Step7, nicht Step9
open import Structures.Step7_DriftGraph using (DriftGraph)
-- Step9 für SpatialSlice
open import Structures.Step9_SpatialStructure using 
  ( SpatialSlice; build-spatial-slice; same-rank-nodes )

----------------------------------------------------------------------
-- 1) 3D-Koordinaten für Rank-3-Detektion
----------------------------------------------------------------------

record ℤ³ : Set where
  constructor mk3
  field
    x  : ℤ
    y  : ℤ 
    z₃ : ℤ

toZ3 : ℕ × ℕ × ℕ → ℤ³
toZ3 (a , b , c) = mk3 (+_ a) (+_ b) (+_ c)

----------------------------------------------------------------------
-- 2) ℤ-Arithmetik und 3D-Determinante
----------------------------------------------------------------------

negℤ : ℤ → ℤ
negℤ (+_ zero) = +_ zero
negℤ (+_ (suc n)) = -[1+ n ]  
negℤ (-[1+ n ]) = +_ (suc n)

-- KORRIGIERT: Nutze importierte Operatoren
_∗ℤ_ : ℤ → ℤ → ℤ
_∗ℤ_ = _*ℤ_

_−ℤ_ : ℤ → ℤ → ℤ  
_−ℤ_ = _-ℤ_

-- 3D-Determinante
det3 : ℤ³ → ℤ³ → ℤ³ → ℤ
det3 u v w = 
  (ℤ³.x u) ∗ℤ ((ℤ³.y v) ∗ℤ (ℤ³.z₃ w) −ℤ (ℤ³.z₃ v) ∗ℤ (ℤ³.y w)) −ℤ
  (ℤ³.y u) ∗ℤ ((ℤ³.x v) ∗ℤ (ℤ³.z₃ w) −ℤ (ℤ³.z₃ v) ∗ℤ (ℤ³.x w)) +ℤ
  (ℤ³.z₃ u) ∗ℤ ((ℤ³.x v) ∗ℤ (ℤ³.y w) −ℤ (ℤ³.y v) ∗ℤ (ℤ³.x w))

nonZeroℤ : ℤ → Bool
nonZeroℤ (+_ zero) = false
nonZeroℤ _ = true

----------------------------------------------------------------------
-- 3) Gute Triple (Rank-3-Charakterisierung)
----------------------------------------------------------------------

record GoodTriple : Set where
  constructor pack  
  field
    u v w : ℤ³
    rest : List ℤ³
    proof : nonZeroℤ (det3 u v w) ≡ true

data HasGoodTriple : List ℤ³ → Set where
  here  : ∀ {u v w rest} → 
          nonZeroℤ (det3 u v w) ≡ true → 
          HasGoodTriple (u ∷ v ∷ w ∷ rest)
  there : ∀ {u rest} → 
          HasGoodTriple rest → 
          HasGoodTriple (u ∷ rest)

----------------------------------------------------------------------
-- 4) Rank-3-Witness und Detektor  
----------------------------------------------------------------------

rank3Witness : List ℤ³ → Maybe GoodTriple
rank3Witness (u ∷ v ∷ w ∷ rs) =
  if nonZeroℤ (det3 u v w)
  then just (pack u v w rs refl)
  else rank3Witness (v ∷ w ∷ rs)
rank3Witness _ = nothing

-- KORRIGIERT: Nutze is-just statt isJust
rank3? : List ℤ³ → Bool
rank3? xs = is-just (rank3Witness xs)

----------------------------------------------------------------------
-- 5) Integration mit SpatialSlice Architektur
----------------------------------------------------------------------

-- Differenzen-Berechnung
diffs : List ℤ³ → List ℤ³
diffs [] = []
diffs (_ ∷ []) = []  
diffs (u ∷ v ∷ rest) = (diff u v) ∷ diffs (v ∷ rest)
  where
    diff : ℤ³ → ℤ³ → ℤ³
    diff u v = mk3 (ℤ³.x v −ℤ ℤ³.x u) (ℤ³.y v −ℤ ℤ³.y u) (ℤ³.z₃ v −ℤ ℤ³.z₃ u)

-- Integration mit eurer SpatialSlice Architektur
Embed3NatAt : DriftGraph → ℕ → List ℤ³  
Embed3NatAt G t = 
  let spatialSlice = build-spatial-slice G t
      -- TODO: Spektrale 3D-Einbettung implementieren
      placeholder3D = map (λ _ → mk3 (+_ 0) (+_ 0) (+_ 0)) spatialSlice
  in  placeholder3D

-- Rank-3-Test auf temporal slice
rank3AtTime : DriftGraph → ℕ → Bool  
rank3AtTime G t = 
  let points3D = Embed3NatAt G t
      diffs3D = diffs points3D
  in  rank3? diffs3D
