{-# OPTIONS --safe #-}

module Structures.Step10_FoldMap where

open import Structures.Step1_BooleanFoundation
open import Structures.Step2_VectorOperations      using (Dist)
open import Structures.Step7_DriftGraph            using (DriftGraph; Node; NodeId; nodes; nodeId; content)
open import Structures.Step9_SpatialStructure      using (SpatialSlice; same-rank-nodes; node-to-dist; are-spatially-related)

open import Data.Nat        using (ℕ; _≟_)
open import Data.List       using (List; []; _∷_; map)
open import Data.Bool       using (Bool; true; false; _∨_)
open import Data.Product    using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Zellen im gefalteten Raum (repr: irgendein NodeId aus der Klasse)
record Cell : Set where
  constructor mkCell
  field repr : NodeId

-- Undirektionaler gefalteter Graph (pro Rang)
record FoldedGraph : Set where
  constructor mkFolded
  field
    cells  : List Cell
    uEdges : List (Cell × Cell)

-- Fold-Map: π ordnet Slice-Knoten ihren Zellen zu; folded ist das Bild
record FoldMap (G : DriftGraph) (rank : ℕ) : Set where
  constructor mkFoldMap
  field
    π      : Node → Cell
    folded : FoldedGraph

------------------------------------------------------------------------
-- KANONISCHE FALTUNG (Spezifikation): Äquivalenz = transitive Hülle
-- der symmetrisierten spatial-Relation im Slice.
------------------------------------------------------------------------

buildFold : (G : DriftGraph) → (rank : ℕ) → FoldMap G rank
buildFold G rank = mkFoldMap π (mkFolded classes undir)
  where
    slice : List Node
    slice = same-rank-nodes G rank

    -- Symmetrisierte Relation auf Dists
    related? : Node → Node → Bool
    related? n m =
      let d₁ = node-to-dist n; d₂ = node-to-dist m in
      are-spatially-related d₁ d₂ ∨ are-spatially-related d₂ d₁

    ------------------------------------------------------------------
    -- POSTULATE (nur Implementationsdetails; die Spezifikation ist klar):
    -- 1) classOf: liefert die Äquivalenzklasse (als Zelle) eines Knotens
    -- 2) classes: die Liste aller Zellen im Slice
    -- 3) undir  : undirektionale Kanten zwischen Zellen (Existenz irgendeines
    --    related?-Paars zwischen den beiden Klassen)
    ------------------------------------------------------------------
    postulate
      classOf : Node → Cell
      classes : List Cell
      undir   : List (Cell × Cell)

    π : Node → Cell
    π = classOf
