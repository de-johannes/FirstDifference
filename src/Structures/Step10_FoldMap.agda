{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Step 10a : Constructive Fold-Map  (rank-preserving quotient)
--            *ohne* Postulate, rein DFS über Listen
------------------------------------------------------------------------

module Structures.Step10_FoldMap where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat        using (ℕ; _≟_; zero; suc)
open import Data.List       using (List; []; _∷_; map; _++_; filter)
open import Data.Bool       using (Bool; true; false; not; _∨_)
open import Data.Product    using (_×_; _,_)
open import Data.Maybe      using (Maybe; just; nothing)

open import Structures.Step1_BooleanFoundation
open import Structures.Step2_VectorOperations      using (Dist)
open import Structures.Step7_DriftGraph            using
  ( DriftGraph ; Node ; NodeId
  ; nodes ; nodeId ; content )
open import Structures.Step9_SpatialStructure      using
  ( same-rank-nodes ; node-to-dist ; are-spatially-related )

------------------------------------------------------------------------
-- 1.   List-Hilfsfunktionen
------------------------------------------------------------------------

_∈_ : {A : Set} → (A → A → Bool) → A → List A → Bool
_∈_ _≟_ x []       = false
_∈_ _≟_ x (y ∷ ys) with _≟_ x y
... | true  = true
... | false = _∈_ _≟_ x ys

nodeEq? : Node → Node → Bool
nodeEq? n m with nodeId n ≟ nodeId m
... | yes _ = true
... | no  _ = false

unionBy : {A : Set} → (A → A → Bool) → List A → List A → List A
unionBy _≟_ xs [] = xs
unionBy _≟_ xs (y ∷ ys) with _∈_ _≟_ y xs
... | true  = unionBy _≟_ xs ys
... | false = unionBy _≟_ (xs ++ y ∷ []) ys

------------------------------------------------------------------------
-- 2.   Nachbarschaft + DFS für die transitive Hülle
------------------------------------------------------------------------

private
  related? : List Node → Node → Node → Bool
  related? slice a b =
    let d₁ = node-to-dist a ; d₂ = node-to-dist b in
    are-spatially-related d₁ d₂ ∨ are-spatially-related d₂ d₁

nbrs : List Node → Node → List Node
nbrs slice n = filter (λ m → related? slice n m) slice

dfs : List Node → List Node → List Node → List Node
dfs slice [] visited = visited
dfs slice (s ∷ stack) visited with _∈_ nodeEq? s visited
... | true  = dfs slice stack visited
... | false = dfs slice (nbrs slice s ++ stack) (s ∷ visited)

connectedComponent : List Node → Node → List Node
connectedComponent slice seed = dfs slice (seed ∷ []) []

------------------------------------------------------------------------
-- 3.   Partition in Äquivalenz­klassen
------------------------------------------------------------------------

partitionComponents : List Node → List (List Node)
partitionComponents [] = []
partitionComponents (n ∷ ns) with _∈_ nodeEq? n (concat ns)
... | true  = partitionComponents ns
... | false =
  let comp  = connectedComponent (n ∷ ns) n
      rest  = filter (λ m → not (_∈_ nodeEq? m comp)) ns
  in  comp ∷ partitionComponents rest
  where
    concat : List (List Node) → List Node
    concat []         = []
    concat (xs ∷ xss) = xs ++ concat xss

------------------------------------------------------------------------
-- 4.   Datentypen für Cell und FoldedGraph
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
-- 5.   Fold-Map bauen
------------------------------------------------------------------------

record FoldMap (G : DriftGraph) (rank : ℕ) : Set where
  constructor mkFoldMap
  field
    π      : Node → Cell
    folded : FoldedGraph

buildFold : (G : DriftGraph) → (rank : ℕ) → FoldMap G rank
buildFold G rank = mkFoldMap π (mkFolded cells uEdges)
  where
    slice  = same-rank-nodes G rank
    comps  = partitionComponents slice

    toCell : List Node → Cell
    toCell []        = mkCell 0
    toCell (n ∷ _)   = mkCell (nodeId n)

    cells  = map toCell comps

    π : Node → Cell
    π n = case findComp comps of λ
        { nothing → mkCell (nodeId n)
        ; just c  → toCell c }
      where
        findComp : List (List Node) → Maybe (List Node)
        findComp [] = nothing
        findComp (c ∷ cs) with _∈_ nodeEq? n c
        ... | true  = just c
        ... | false = findComp cs

    -- True, falls irgendein Paar (a,b) aus den beiden Komponenten räumlich benachbart ist
    compsRelated? : List Node → List Node → Bool
    compsRelated? [] _ = false
    compsRelated? (a ∷ as) bs = relatedAny a bs ∨ compsRelated? as bs
      where
        relatedAny : Node → List Node → Bool
        relatedAny _ []       = false
        relatedAny x (y ∷ ys) = related? slice x y ∨ relatedAny x ys

    makeUEdges : List (List Node) → List (Cell × Cell)
    makeUEdges []       = []
    makeUEdges (c ∷ cs) = mapMaybe (edgeIfRelated c) cs ++ makeUEdges cs
      where
        edgeIfRelated : List Node → List Node → Maybe (Cell × Cell)
        edgeIfRelated c₁ c₂ with compsRelated? c₁ c₂
        ... | true  = just (toCell c₁ , toCell c₂)
        ... | false = nothing

        mapMaybe : {A B : Set} → (A → Maybe B) → List A → List B
        mapMaybe f []       = []
        mapMaybe f (x ∷ xs) with f x
        ... | just y   = y ∷ mapMaybe f xs
        ... | nothing  = mapMaybe f xs

    uEdges = makeUEdges comps
