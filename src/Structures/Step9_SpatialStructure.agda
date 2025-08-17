{-# OPTIONS --safe #-}

module Structures.Step9_SpatialStructure where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≟_)
open import Data.List using (List; []; _∷_; filter; map; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)

-- Import your existing structures
open import Structures.Step7_DriftGraph as DG using 
  (DriftGraph; Node; NodeId; nodeId; nodes; edges; _—→_within_; _can-reach_within_)
open import Structures.Step8_PathCategory as PC using 
  (Path; refl-path; _∷-path_; DriftPathCategory)

------------------------------------------------------------------------
-- 1. TEMPORAL SLICES: Nodes grouped by rank/time
------------------------------------------------------------------------

-- | Extract all nodes at a specific temporal rank
slice-at-rank : DriftGraph → ℕ → List Node  
slice-at-rank G rank = filter (λ n → is-at-rank (nodeId n) rank) (nodes G)
  where
    is-at-rank : NodeId → ℕ → Bool
    is-at-rank id target with id ≟ target
    ... | yes _ = true
    ... | no  _ = false

-- | A temporal slice: spatial configuration at fixed time
record TemporalSlice : Set where
  constructor mk-slice
  field
    slice-nodes : List Node
    rank : ℕ

-- | Extract slice from DriftGraph at given rank
get-slice : DriftGraph → ℕ → TemporalSlice
get-slice G r = mk-slice (slice-at-rank G r) r

------------------------------------------------------------------------
-- 2. CO-PARENT RELATIONS: The key insight for spatial structure
------------------------------------------------------------------------

-- | Two nodes are co-parents if they share a common descendant
-- | This creates the "spatial" connection within temporal slices
data CoParent (G : DriftGraph) (u v : Node) : Set where
  shared-child : ∀ (child : Node) →
                 nodeId u DG.—→ nodeId child within G →
                 nodeId v DG.—→ nodeId child within G →
                 CoParent G u v

-- | Helper for list membership
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- | Boolean disjunction
_∨_ : Bool → Bool → Bool
true ∨ _ = true
false ∨ b = b

-- | Check edge equality
eq-edge : (ℕ × ℕ) → (ℕ × ℕ) → Bool
eq-edge (a₁ , b₁) (a₂ , b₂) with a₁ ≟ a₂ | b₁ ≟ b₂
... | yes _ | yes _ = true
... | _ | _ = false

-- | Check if edge is in edge list
elem-edge : (ℕ × ℕ) → List (ℕ × ℕ) → Bool
elem-edge e [] = false
elem-edge e (x ∷ xs) = eq-edge e x ∨ elem-edge e xs

-- | Check if there's an edge from parent to child
has-edge-from : DriftGraph → Node → Node → Bool
has-edge-from G parent child = 
  elem-edge (nodeId parent , nodeId child) (edges G)

-- | Check if two nodes are co-parents (decidable version)
are-coparents? : DriftGraph → Node → Node → Bool
are-coparents? G u v = has-shared-child (nodes G)
  where
    has-shared-child : List Node → Bool
    has-shared-child [] = false
    has-shared-child (n ∷ ns) = 
      if (has-edge-from G u n) ∧ (has-edge-from G v n)
      then true
      else has-shared-child ns

------------------------------------------------------------------------
-- 3. SPATIAL ADJACENCY MATRIX: From co-parent relations to geometry
------------------------------------------------------------------------

-- | Spatial adjacency within a temporal slice
-- | This is the undirected graph that will yield our Laplacian
record SpatialGraph : Set where
  constructor mk-spatial
  field
    spatial-nodes : List Node
    spatial-edges : List (Node × Node)  -- Undirected edges

-- | Compute co-parent edges within a list of nodes
compute-coparent-edges : DriftGraph → List Node → List (Node × Node)
compute-coparent-edges G [] = []
compute-coparent-edges G (n ∷ ns) = 
  map (λ m → (n , m)) (filter (are-coparents? G n) ns) 
  ++ compute-coparent-edges G ns

-- | Build spatial graph from temporal slice using co-parent relations
build-spatial-graph : DriftGraph → ℕ → SpatialGraph
build-spatial-graph G rank = 
  mk-spatial slice-nodes coparent-edges
  where
    slice = get-slice G rank
    slice-nodes = TemporalSlice.slice-nodes slice
    coparent-edges = compute-coparent-edges G slice-nodes

------------------------------------------------------------------------
-- 4. BASIC PROPERTIES AND VERIFICATION
------------------------------------------------------------------------

-- | Verification: Co-parent relation is symmetric
coparent-symmetric : ∀ G u v → CoParent G u v → CoParent G v u
coparent-symmetric G u v (shared-child child u→child v→child) = 
  shared-child child v→child u→child

-- | Test with your example graph
test-spatial-at-rank-0 : SpatialGraph
test-spatial-at-rank-0 = build-spatial-graph DG.example-graph 0

test-spatial-at-rank-1 : SpatialGraph
test-spatial-at-rank-1 = build-spatial-graph DG.example-graph 1

test-spatial-at-rank-2 : SpatialGraph
test-spatial-at-rank-2 = build-spatial-graph DG.example-graph 2

-- | Extract spatial nodes at rank 2 (should contain node₂)
test-slice-2 : TemporalSlice
test-slice-2 = get-slice DG.example-graph 2

------------------------------------------------------------------------
-- 5. FOUNDATION FOR SPECTRAL ANALYSIS
------------------------------------------------------------------------

-- | Count nodes in a list
list-length : {A : Set} → List A → ℕ
list-length [] = zero
list-length (_ ∷ xs) = suc (list-length xs)

-- | Get the size of spatial graph
spatial-size : SpatialGraph → ℕ
spatial-size sg = list-length (SpatialGraph.spatial-nodes sg)

-- | Placeholder for spectral embedding coordinate
Coordinate = ℕ × ℕ × ℕ  -- (x,y,z) as rationals approximated by pairs

-- | Placeholder for 3D embedding (to be computed numerically)
embed-3d : SpatialGraph → List Coordinate
embed-3d sg = []  -- Placeholder: will compute via eigenvalues

------------------------------------------------------------------------
-- WORKING FOUNDATION: Ready for spectral analysis
------------------------------------------------------------------------
