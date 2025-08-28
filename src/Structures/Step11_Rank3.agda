{-# OPTIONS --safe #-}

module Structures.Step11_Rank3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.Nat       using (ℕ; zero; suc; _+_; _*_)
-- KORRIGIERT: Importiere alles aus Data.Integer (das re-exportiert Data.Integer.Base)
open import Data.Integer   using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.List      using (List; []; _∷_; map)
open import Data.Maybe     using (Maybe; just; nothing)
open import Data.Maybe.Base using (is-just)
open import Data.Product   using (_×_; _,_)

-- Korrekte Module-Imports
open import Structures.Step7_DriftGraph using (DriftGraph)
open import Structures.Step9_SpatialStructure using 
  ( SpatialSlice; build-spatial-slice; same-rank-nodes )

----------------------------------------------------------------------
-- 1) 3D-Koordinaten
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
-- 2) ℤ-Arithmetik - KORRIGIERT: Nutze die standard Operatoren
----------------------------------------------------------------------

negℤ : ℤ → ℤ
negℤ (+_ zero) = +_ zero
negℤ (+_ (suc n)) = -[1+ n ]  
negℤ (-[1+ n ]) = +_ (suc n)

-- KORRIGIERT: Die Operatoren heißen einfach _+_, _-_, _*_ in Data.Integer
_∗ℤ_ : ℤ → ℤ → ℤ
_∗ℤ_ = _*_

_−ℤ_ : ℤ → ℤ → ℤ  
_−ℤ_ = _-_

_+ℤ_ : ℤ → ℤ → ℤ
_+ℤ_ = _+_

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
-- 3) Rest bleibt gleich...
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

rank3Witness : List ℤ³ → Maybe GoodTriple
rank3Witness (u ∷ v ∷ w ∷ rs) =
  if nonZeroℤ (det3 u v w)
  then just (pack u v w rs refl)
  else rank3Witness (v ∷ w ∷ rs)
rank3Witness _ = nothing

rank3? : List ℤ³ → Bool
rank3? xs = is-just (rank3Witness xs)

diffs : List ℤ³ → List ℤ³
diffs [] = []
diffs (_ ∷ []) = []  
diffs (u ∷ v ∷ rest) = (diff u v) ∷ diffs (v ∷ rest)
  where
    diff : ℤ³ → ℤ³ → ℤ³
    diff u v = mk3 (ℤ³.x v −ℤ ℤ³.x u) (ℤ³.y v −ℤ ℤ³.y u) (ℤ³.z₃ v −ℤ ℤ³.z₃ u)

Embed3NatAt : DriftGraph → ℕ → List ℤ³  
Embed3NatAt G t = 
  let spatialSlice = build-spatial-slice G t
      placeholder3D = map (λ _ → mk3 (+_ 0) (+_ 0) (+_ 0)) spatialSlice
  in  placeholder3D

rank3AtTime : DriftGraph → ℕ → Bool  
rank3AtTime G t = 
  let points3D = Embed3NatAt G t
      diffs3D = diffs points3D
  in  rank3? diffs3D
