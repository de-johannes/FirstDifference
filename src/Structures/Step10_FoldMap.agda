{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Step 10a : Constructive Fold-Map  (rank-preserving quotient)
--  * terminierend (Fuel-Parameter)
--  * reiner Listen-DFS, keine Postulate / kein if-Sugar
--  * kompatibel mit Stdlib, in der Data.List.filter Dec erwartet
------------------------------------------------------------------------

module Structures.Step10_FoldMap where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary                      using (Dec; yes; no)
open import Data.Nat                              using (ℕ; _≟_; zero; suc; _+_; _≤?_)
open import Data.List                             using (List; []; _∷_; map; _++_; length)
open import Data.Bool                             using (Bool; true; false; not; _∨_)
open import Data.Product                          using (_×_; _,_)
open import Data.Maybe                            using (Maybe; just; nothing)

open import Structures.Step1_BooleanFoundation
open import Structures.Step2_VectorOperations      using (Dist)
open import Structures.Step7_DriftGraph            using
  ( DriftGraph ; Node ; NodeId
  ; nodes ; nodeId ; content )
open import Structures.Step9_SpatialStructure      using
  ( same-rank-nodes ; node-to-dist ; are-spatially-related )

------------------------------------------------------------------------
-- 0.   Dec → Bool  & Nat-/Node-Vergleich
------------------------------------------------------------------------

decToBool : {A : Set} → Dec A → Bool
decToBool (yes _) = true
decToBool (no  _) = false

_==ᴮ_ : ℕ → ℕ → Bool
m ==ᴮ n = decToBool (m ≟ n)

nodesEqᵇ : Node → Node → Bool
nodesEqᵇ a b = (nodeId a) ==ᴮ (nodeId b)

------------------------------------------------------------------------
-- 1.   Listen-Utilities (Bool-Variante)
------------------------------------------------------------------------

elemBy : {A : Set} → (A → A → Bool) → A → List A → Bool
elemBy _≈_ x []       = false
elemBy _≈_ x (y ∷ ys) with _≈_ x y
... | true  = true
... | false = elemBy _≈_ x ys

remove1By : {A : Set} → (A → A → Bool) → A → List A → List A
remove1By _≈_ x []       = []
remove1By _≈_ x (y ∷ ys) with _≈_ x y
... | true  = ys
... | false = y ∷ remove1By _≈_ x ys

removeAllBy : {A : Set} → (A → A → Bool) → List A → List A → List A
removeAllBy _≈_ []       xs = xs
removeAllBy _≈_ (z ∷ zs) xs = removeAllBy _≈_ zs (remove1By _≈_ z xs)

mapMaybe : {A B : Set} → (A → Maybe B) → List A → List B
mapMaybe f []       = []
mapMaybe f (x ∷ xs) with f x
... | just y   = y ∷ mapMaybe f xs
... | nothing  = mapMaybe f xs

concat : {A : Set} → List (List A) → List A
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

filterBy : {A : Set} → (A → Bool) → List A → List A
filterBy p []       = []
filterBy p (x ∷ xs) with p x
... | true  = x ∷ filterBy p xs
... | false =     filterBy p xs

------------------------------------------------------------------------
-- 2.   Symmetrisierte Nachbarschaft
------------------------------------------------------------------------

relatedᵇ : Node → Node → Bool
relatedᵇ a b =
  let d₁ = node-to-dist a ; d₂ = node-to-dist b in
  are-spatially-related d₁ d₂ ∨ are-spatially-related d₂ d₁

nbrs : List Node → Node → List Node
nbrs slice n = filterBy (λ m → relatedᵇ n m) slice

------------------------------------------------------------------------
-- 3.   DFS mit Fuel (terminierend)
------------------------------------------------------------------------

dfsFuel : List Node → List Node → List Node → ℕ → List Node
dfsFuel slice stack visited zero    = visited
dfsFuel slice []    visited (suc f) = visited
dfsFuel slice (s ∷ st) visited (suc f) with elemBy nodesEqᵇ s visited
... | true  = dfsFuel slice st visited f
... | false = dfsFuel slice (nbrs slice s ++ st) (s ∷ visited) f

connectedComponent : List Node → Node → List Node
connectedComponent slice seed =
  dfsFuel slice (seed ∷ []) [] (length slice + 1)

------------------------------------------------------------------------
-- 4.   Partition des Slices in Komponenten (mit Fuel)
------------------------------------------------------------------------

componentsFromFuel : List Node → List (List Node) → ℕ → List (List Node)
componentsFromFuel slice acc zero       = acc
componentsFromFuel slice acc (suc fuel) with slice
... | []         = acc
... | (u ∷ rest) with elemBy nodesEqᵇ u (concat acc)
... | true  = componentsFromFuel rest acc fuel
... | false =
  let comp   = connectedComponent (u ∷ rest) u
      rest'  = removeAllBy nodesEqᵇ comp rest
      acc'   = comp ∷ acc
  in  componentsFromFuel rest' acc' fuel

componentsFrom : List Node → List (List Node)
componentsFrom slice = componentsFromFuel slice [] (length slice)

------------------------------------------------------------------------
-- 5.   Datentypen für Cells & FoldedGraph
------------------------------------------------------------------------

record Cell : Set where
  constructor mkCell
  field repr : NodeId

cellEqᵇ : Cell → Cell → Bool
cellEqᵇ c₁ c₂ = (Cell.repr c₁) ==ᴮ (Cell.repr c₂)

record FoldedGraph : Set where
  constructor mkFolded
  field
    cells  : List Cell
    uEdges : List (Cell × Cell)

------------------------------------------------------------------------
-- 6.   Fold-Map  (π + gefalteter Raum)
------------------------------------------------------------------------

record FoldMap (G : DriftGraph) (rank : ℕ) : Set where
  constructor mkFoldMap
  field
    π      : Node → Cell
    folded : FoldedGraph

buildFold : (G : DriftGraph) → (rank : ℕ) → FoldMap G rank
buildFold G rank = mkFoldMap π (mkFolded cells uEdges)
  where
    slice  : List Node
    slice  = same-rank-nodes G rank

    comps : List (List Node)
    comps = componentsFrom slice

    toCell : List Node → Cell
    toCell []      = mkCell 0
    toCell (n ∷ _) = mkCell (nodeId n)

    cells : List Cell
    cells = map toCell comps

    findComp : Node → List (List Node) → Maybe (List Node)
    findComp n []       = nothing
    findComp n (c ∷ cs) with elemBy nodesEqᵇ n c
    ... | true  = just c
    ... | false = findComp n cs

    π : Node → Cell
    π n with findComp n comps
    ... | just c  = toCell c
    ... | nothing = mkCell (nodeId n)

    compsRelatedᵇ : List Node → List Node → Bool
    compsRelatedᵇ []       _  = false
    compsRelatedᵇ (a ∷ as) bs = anyRelated a bs ∨ compsRelatedᵇ as bs
      where
        anyRelated : Node → List Node → Bool
        anyRelated _ []       = false
        anyRelated x (y ∷ ys) = relatedᵇ x y ∨ anyRelated x ys

    buildUEdges : List (List Node) → List (Cell × Cell)
    buildUEdges []       = []
    buildUEdges (c ∷ cs) =
      mapMaybe (edgeIfRelated c) cs ++ buildUEdges cs
      where
        edgeIfRelated : List Node → List Node → Maybe (Cell × Cell)
        edgeIfRelated c₁ c₂ with compsRelatedᵇ c₁ c₂
        ... | true  = just (toCell c₁ , toCell c₂)
        ... | false = nothing

    uEdges : List (Cell × Cell)
    uEdges = buildUEdges comps
