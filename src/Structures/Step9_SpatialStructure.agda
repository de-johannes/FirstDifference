{-# OPTIONS --safe #-}

module Structures.Step9_SpatialStructure where

-- Use YOUR existing foundation
open import Structures.Step1_BooleanFoundation
open import Structures.Step2_VectorOperations using (Dist; drift; join; neg; all-false)
open import Structures.Step4_PartialOrder using (_≤ᵈ_)
open import Structures.Step5_CategoryStructure using (DriftMorphism; idDrift; composeDrift)
open import Structures.Step6_SemanticTimeFunctor using (Sequence; evolve; TimeFunctor)
open import Structures.Step7_DriftGraph using (DriftGraph; Node; NodeId; nodes; edges; nodeId; content)
open import Structures.Step8_PathCategory using (Path; DriftPathCategory)

-- Standard library
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; zipWith)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- HELPER: Boolean Filter Function
------------------------------------------------------------------------

bool-filter : ∀ {A : Set} → (A → Bool) → List A → List A
bool-filter p [] = []
bool-filter p (x ∷ xs) = if p x then x ∷ bool-filter p xs else bool-filter p xs

------------------------------------------------------------------------
-- SPATIAL SLICES: Fixed to dimension 2 (matching your Node type)
------------------------------------------------------------------------

-- | A spatial slice: 2D distinctions at the same temporal rank
SpatialSlice : ℕ → Set  -- Removed the second parameter since we're fixing dimension
SpatialSlice rank = List (Dist (suc (suc zero)))  -- Fixed to dimension 2

-- | Extract nodes of same rank from DriftGraph
same-rank-nodes : DriftGraph → ℕ → List Node
same-rank-nodes G target-rank = 
  bool-filter (λ node → rank-matches (nodeId node) target-rank) (nodes G)
  where
    rank-matches : NodeId → ℕ → Bool
    rank-matches id target with id ≟ target
    ... | yes _ = true
    ... | no  _ = false

-- | Convert Node content to Dist - now matches the actual Node type
node-to-dist : Node → Dist (suc (suc zero))
node-to-dist node = content node

-- | Build spatial slice using your existing structures
build-spatial-slice : DriftGraph → ℕ → SpatialSlice 0  -- Fixed to match type
build-spatial-slice G rank = 
  map node-to-dist (same-rank-nodes G rank)

------------------------------------------------------------------------
-- SPATIAL MORPHISMS: Fixed to dimension 2
------------------------------------------------------------------------

-- | Check if a 2D Dist has any true components
has-true : Dist (suc (suc zero)) → Bool
has-true [] = false
has-true (true ∷ xs) = true
has-true (false ∷ xs) = has-true xs

-- | Check if two 2D distinctions are spatially related via drift
are-spatially-related : Dist (suc (suc zero)) → Dist (suc (suc zero)) → Bool
are-spatially-related d₁ d₂ = has-true (drift d₁ d₂)

-- | Spatial adjacency for 2D distinctions
spatial-adjacency : SpatialSlice 0 → List (Dist (suc (suc zero)) × Dist (suc (suc zero)))
spatial-adjacency slice = build-pairs slice slice
  where
    build-pairs : List (Dist (suc (suc zero))) → List (Dist (suc (suc zero))) → 
                  List (Dist (suc (suc zero)) × Dist (suc (suc zero)))
    build-pairs [] _ = []
    build-pairs (d ∷ ds) slice₂ = 
      filter-related d slice₂ ++ build-pairs ds slice₂
      where
        filter-related : Dist (suc (suc zero)) → List (Dist (suc (suc zero))) → 
                         List (Dist (suc (suc zero)) × Dist (suc (suc zero)))
        filter-related d [] = []
        filter-related d (d₂ ∷ ds₂) = 
          if are-spatially-related d d₂ 
          then (d , d₂) ∷ filter-related d ds₂
          else filter-related d ds₂

------------------------------------------------------------------------
-- INTEGRATION: Works with your existing 2D structures
------------------------------------------------------------------------

-- | Apply 2D drift morphisms to spatial slices
test-spatial-temporal : ∀ {n} → DriftMorphism (suc (suc zero)) n → 
                        SpatialSlice 0 → List (Dist n)
test-spatial-temporal φ slice = 
  map (DriftMorphism.f φ) slice

-- | Spatial evolution over time using your TimeFunctor
spatial-temporal-evolution : ∀ {n t} → DriftMorphism (suc (suc zero)) n → 
                             List (SpatialSlice t) → List (List (Dist n))
spatial-temporal-evolution φ slices = 
  map (test-spatial-temporal φ) slices

------------------------------------------------------------------------
-- EXAMPLE: Working with your existing 2D structures
------------------------------------------------------------------------

-- | Example: Create a simple 2D spatial slice
example-spatial-slice : SpatialSlice 0
example-spatial-slice = (true ∷ false ∷ []) ∷ 
                        (false ∷ true ∷ []) ∷ 
                        (true ∷ true ∷ []) ∷ []

-- | Test: Check spatial relationships
test-spatial-relation : Bool
test-spatial-relation = are-spatially-related (true ∷ false ∷ []) (false ∷ true ∷ [])
