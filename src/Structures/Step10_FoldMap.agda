{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Step 10: Constructive Fold-Map (rank-preserving quotient)
------------------------------------------------------------------------
--   From a spatial slice (Step 9) to an undirected FoldedGraph
--   with explicit DFS-based connected-component construction.
------------------------------------------------------------------------

module Structures.Step10_FoldMap where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat        using (ℕ; _≟_; zero; suc)
open import Data.List       using (List; []; _∷_; map; _++_; filter)
open import Data.Bool       using (Bool; true; false; _∨_)
open import Data.Product    using (_×_; _,_)
open import Data.Maybe      using (Maybe; nothing; just)

open import Structures.Step1_BooleanFoundation
open import Structures.Step2_VectorOperations      using (Dist)
open import Structures.Step7_DriftGraph            using
  ( DriftGraph ; Node ; NodeId
  ; nodes       -- : DriftGraph → List Node
  ; nodeId      -- : Node → NodeId
  ; content     -- : Node → Dist _
  )
open import Structures.Step9_SpatialStructure      using
  ( same-rank-nodes
  ; node-to-dist
  ; are-spatially-related
  )

------------------------------------------------------------------------
-- 1. Helper — basic list membership & set-like utilities
------------------------------------------------------------------------

_∈_ : {A : Set} → (A → A → Bool) → A → List A → Bool
_∈_ _≟_ x []       = false
_∈_ _≟_ x (y ∷ ys) = if _≟_ x y then true else _∈_ _≟_ x ys

-- decidable equality on Node via NodeId
node-eq? : Node → Node → Bool
node-eq? n m with nodeId n ≟ nodeId m
... | yes _ = true
... | no  _ = false

-- union of two lists w.r.t. a decidable equality (no duplicates)
unionBy : {A : Set} → (A → A → Bool) → List A → List A → List A
unionBy _≟_ xs []       = xs
unionBy _≟_ xs (y ∷ ys) = if y ∈ xs then unionBy _≟_ xs ys
                                       else unionBy _≟_ (xs ++ (y ∷ [])) ys
  where
    _∈ xs = _∈_ _≟_ y xs

------------------------------------------------------------------------
-- 2. DFS — transitive closure of the symmetrised spatial relation
------------------------------------------------------------------------

-- neighbourhood of a Node inside the current slice
nbrs : List Node → Node → List Node
nbrs slice n =
  filter (λ m → related n m) slice
  where
    related : Node → Node → Bool
    related a b =
      let d₁ = node-to-dist a
          d₂ = node-to-dist b
      in are-spatially-related d₁ d₂ ∨ are-spatially-related d₂ d₁

-- depth-first search to collect a connected component
dfs : List Node → List Node → List Node → List Node
dfs slice []      visited = visited
dfs slice (s ∷ stack) visited =
  if s ∈ visited
     then dfs slice stack visited
     else dfs slice (nbrs slice s ++ stack) (s ∷ visited)
  where
    _∈ = _∈_ node-eq?

connectedComponent : List Node → Node → List Node
connectedComponent slice seed = dfs slice (seed ∷ []) []

------------------------------------------------------------------------
-- 3. Partition the slice into components (no duplicates)
------------------------------------------------------------------------

partitionComponents : List Node → List (List Node)
partitionComponents []       = []
partitionComponents (n ∷ ns) with n ∈ visited?
  where
    visited? = foldr _++_ [] (partitionComponents ns)
... | true  = partitionComponents ns
... | false =
      let comp = connectedComponent (n ∷ ns) n
          rest = filter (λ m → not (m ∈ comp?)) ns
      in comp ∷ partitionComponents rest
  where
    _∈ = _∈_ node-eq?
    comp? = comp    -- local alias

------------------------------------------------------------------------
-- 4. FoldedGraph — data types
------------------------------------------------------------------------

record Cell : Set where
  constructor mkCell
  field repr : NodeId

cellEq? : Cell → Cell → Bool
cellEq? c₁ c₂ with repr c₁ ≟ repr c₂
... | yes _ = true
... | no  _ = false

record FoldedGraph : Set where
  constructor mkFolded
  field
    cells  : List Cell
    uEdges : List (Cell × Cell)

------------------------------------------------------------------------
-- 5. Build Fold-Map for a given rank
------------------------------------------------------------------------

record FoldMap (G : DriftGraph) (rank : ℕ) : Set where
  constructor mkFoldMap
  field
    π      : Node → Cell        -- projection
    folded : FoldedGraph        -- quotient space

buildFold : (G : DriftGraph) → (rank : ℕ) → FoldMap G rank
buildFold G rank = mkFoldMap π folded
  where
    slice : List Node
    slice = same-rank-nodes G rank

    comps : List (List Node)
    comps = partitionComponents slice

    toCell : List Node → Cell
    toCell []       = mkCell 0
    toCell (n ∷ _)  = mkCell (nodeId n)

    cells : List Cell
    cells = map toCell comps

    -- map Node → Cell (used by π)
    π : Node → Cell
    π n with findComp comps
      where
        findComp : List (List Node) → Maybe (List Node)
        findComp []       = nothing
        findComp (c ∷ cs) = if n ∈ c? then just c else findComp cs
          where _∈ = _∈_ node-eq?

    ... | nothing  = mkCell (nodeId n)      -- (should not occur if rank-pres.)
    ... | just c   = toCell c

    -- undirected edges between distinct cells if any pair is related
    pairRelated? : List Node → List Node → Bool
    pairRelated? [] _ = false
    pairRelated? (x ∷ xs) ys = (anyRel x ys) ∨ pairRelated? xs ys
      where
        anyRel : Node → List Node → Bool
        anyRel _ []       = false
        anyRel a (b ∷ bs) =
          let d₁ = node-to-dist a
              d₂ = node-to-dist b
          in are-spatially-related d₁ d₂ ∨ are-spatially-related d₂ d₁ ∨ anyRel a bs

    uEdges : List (Cell × Cell)
    uEdges = buildPairs comps
      where
        buildPairs : List (List Node) → List (Cell × Cell)
        buildPairs []       = []
        buildPairs (c ∷ cs) =
          (mapMaybe (edgeIfRelated c) cs) ++ buildPairs cs

        edgeIfRelated : List Node → List Node → Maybe (Cell × Cell)
        edgeIfRelated c₁ c₂ =
          if pairRelated? c₁ c₂ then just (toCell c₁ , toCell c₂) else nothing

        mapMaybe : {A B : Set} → (A → Maybe B) → List A → List B
        mapMaybe f []       = []
        mapMaybe f (x ∷ xs) with f x
        ... | nothing  = mapMaybe f xs
        ... | just y   = y ∷ mapMaybe f xs

    folded : FoldedGraph
    folded = mkFolded cells uEdges
