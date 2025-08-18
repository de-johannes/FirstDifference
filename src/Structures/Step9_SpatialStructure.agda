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
open import Data.List using (List; []; _∷_; filter; map; _++_)
open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; zipWith)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- SPATIAL SLICES: Use your existing Dist structure  
------------------------------------------------------------------------

-- | A spatial slice: distinctions at the same temporal rank
SpatialSlice : ℕ → ℕ → Set
SpatialSlice n rank = List (Dist n)

-- | Extract nodes of same rank from DriftGraph
same-rank-nodes : DriftGraph → ℕ → List Node
same-rank-nodes G target-rank = 
  filter (λ node → rank-matches (nodeId node) target-rank) (nodes G)
  where
    rank-matches : NodeId → ℕ → Bool
    rank-matches id target with id ≟ target
    ... | yes _ = true
    ... | no  _ = false

-- | Convert Node content to Dist
node-to-dist : ∀ {n} → Node → Dist n  
node-to-dist node = content node

-- | Build spatial slice using your existing structures
build-spatial-slice : ∀ {n} → DriftGraph → ℕ → SpatialSlice n 0
build-spatial-slice {n} G rank = 
  map node-to-dist (same-rank-nodes G rank)

------------------------------------------------------------------------
-- SPATIAL MORPHISMS: SIMPLIFIED IMPLEMENTATION
------------------------------------------------------------------------

-- | Check if a Dist has any true components (simpler approach)
has-true : ∀ {n} → Dist n → Bool
has-true [] = false
has-true (true ∷ xs) = true
has-true (false ∷ xs) = has-true xs

-- | Check if two distinctions are spatially related via drift
are-spatially-related : ∀ {n} → Dist n → Dist n → Bool
are-spatially-related d₁ d₂ = has-true (drift d₁ d₂)

-- | Spatial adjacency using your drift-based relationships
spatial-adjacency : ∀ {n} → SpatialSlice n 0 → List (Dist n × Dist n)
spatial-adjacency slice = build-pairs slice slice
  where
    build-pairs : ∀ {n} → List (Dist n) → List (Dist n) → List (Dist n × Dist n)
    build-pairs [] _ = []
    build-pairs (d ∷ ds) slice₂ = 
      filter-related d slice₂ ++ build-pairs ds slice₂
      where
        filter-related : ∀ {n} → Dist n → List (Dist n) → List (Dist n × Dist n)
        filter-related d [] = []
        filter-related d (d₂ ∷ ds₂) = 
          if are-spatially-related d d₂ 
          then (d , d₂) ∷ filter-related d ds₂
          else filter-related d ds₂

------------------------------------------------------------------------
-- INTEGRATION: Works with your existing Steps
------------------------------------------------------------------------

-- | Apply drift morphisms to spatial slices
test-spatial-temporal : ∀ {m n} → DriftMorphism m n → 
                        SpatialSlice m 0 → SpatialSlice n 0  
test-spatial-temporal φ slice = 
  map (DriftMorphism.f φ) slice

-- | Spatial evolution over time using your TimeFunctor
spatial-temporal-evolution : ∀ {m n t} → DriftMorphism m n → 
                             List (SpatialSlice m t) → List (SpatialSlice n t)
spatial-temporal-evolution φ slices = 
  map (test-spatial-temporal φ) slices
