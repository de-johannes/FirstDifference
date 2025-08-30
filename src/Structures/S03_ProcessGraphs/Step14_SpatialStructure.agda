{-# OPTIONS --safe #-}

-- | Step 14: Spatial Structure from Simultaneity
-- | Spatial slices = sets of nodes at equal temporal rank.
-- | Demonstrates how adjacency emerges from drift relations
-- | restricted to a fixed rank.
module Structures.S03_ProcessGraphs.Step14_SpatialStructure where

-- Boolean/distinction foundation
open import Structures.S01_BooleanCore.Step02_VectorOperations using (Dist; drift; join; neg)

-- Order & graph imports
open import Structures.S03_ProcessGraphs.Step10_DriftGraph using (DriftGraph; Node; NodeId; nodes; content)

-- Standard library
open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_) 
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Boolean filter helper
------------------------------------------------------------------------

bool-filter : ∀ {A : Set} → (A → Bool) → List A → List A
bool-filter p []       = []
bool-filter p (x ∷ xs) = if p x then x ∷ bool-filter p xs else bool-filter p xs

------------------------------------------------------------------------
-- Spatial slices
------------------------------------------------------------------------

-- | A spatial slice: distinctions of dimension 2 at same rank
SpatialSlice : ℕ → Set
SpatialSlice rank = List (Dist 2)

-- | Extract nodes of same rank from DriftGraph
same-rank-nodes : DriftGraph → ℕ → List Node
same-rank-nodes G target = 
  bool-filter (λ n → rank-match (nodeId n)) (nodes G)
  where
    rank-match : NodeId → Bool
    rank-match id with id ≟ target
    ... | yes _ = true
    ... | no  _ = false

-- | Convert Node content to Dist
node→dist : Node → Dist 2
node→dist n = content n

-- | Build spatial slice
build-spatial-slice : DriftGraph → ℕ → SpatialSlice 0
build-spatial-slice G r = map node→dist (same-rank-nodes G r)

------------------------------------------------------------------------
-- Spatial adjacency
------------------------------------------------------------------------

-- | Check if a 2D Dist has any true components
has-true : Dist 2 → Bool
has-true (x ∷ y ∷ []) = x ∨ y

-- | Check if two 2D distinctions are spatially related
are-spatially-related : Dist 2 → Dist 2 → Bool
are-spatially-related d₁ d₂ = has-true (drift d₁ d₂)

-- | Spatial adjacency pairs
spatial-adjacency : SpatialSlice 0 → List (Dist 2 × Dist 2)
spatial-adjacency slice = build-pairs slice slice
  where
    build-pairs : List (Dist 2) → List (Dist 2) → List (Dist 2 × Dist 2)
    build-pairs [] _          = []
    build-pairs (d ∷ ds) all₂ = filter-rel d all₂ ++ build-pairs ds all₂

    filter-rel : Dist 2 → List (Dist 2) → List (Dist 2 × Dist 2)
    filter-rel d []       = []
    filter-rel d (d₂ ∷ r) =
      if are-spatially-related d d₂
      then (d , d₂) ∷ filter-rel d r
      else filter-rel d r

------------------------------------------------------------------------
-- Example
------------------------------------------------------------------------

example-slice : SpatialSlice 0
example-slice = (true ∷ false ∷ []) ∷ 
                (false ∷ true ∷ []) ∷ 
                (true ∷ true ∷ []) ∷ []

test-rel : Bool
test-rel = are-spatially-related (true ∷ false ∷ []) (false ∷ true ∷ [])