{-# OPTIONS --safe #-}

-- Step 14: Spatial structure – Soundness & Completeness of the rank filter
-- We prove that same-rank-nodes picks exactly the nodes whose nodeId = rank.

module Structures.S03_ProcessGraphs.Step14_SpatialStructure_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation using (Bool; true; false)

-- Bring in list-membership and graph essentials
open import Structures.S03_ProcessGraphs.Step10_DriftGraph
  using (DriftGraph; Node; NodeId; nodeId; nodes; _∈_; here; there)

-- Bring in the spatial constructors we reason about
open import Structures.S03_ProcessGraphs.Step14_SpatialStructure
  using (bool-filter; same-rank-nodes; rank-match; rank-match-true)

------------------------------------------------------------------------
-- Elementary contradictions for Bool and rank-match soundness
------------------------------------------------------------------------

-- No confusion between false and true
false≠true : false ≡ true → ⊥
false≠true ()

-- If rank-match id target ≡ true then id ≡ target
rank-match-sound : ∀ {id target : ℕ} → rank-match id target ≡ true → id ≡ target
rank-match-sound {id} {target} rm≡ with id ≟ target
... | yes eq = eq
... | no  _  = ⊥-elim (false≠true rm≡)

------------------------------------------------------------------------
-- Specialization to same-rank-nodes
------------------------------------------------------------------------

-- Soundness: every member filtered by same-rank-nodes has matching rank.
same-rank-sound :
  ∀ {G : DriftGraph} {r : ℕ} {n : Node} →
  n ∈ same-rank-nodes G r → nodeId n ≡ r
same-rank-sound {G} {r} {n} m = rank-match-sound (go (nodes G) m)
  where
    p : Node → Bool
    p node = rank-match (nodeId node) r

    -- Show: if n ∈ bool-filter p xs then p n ≡ true
    go : ∀ (xs : List Node) → n ∈ bool-filter p xs → p n ≡ true
    go [] ()
    go (y ∷ ys) prf with p y | prf
    ... | true  | here        = refl
    ... | true  | there prf'  = go ys prf'
    ... | false | prf         = go ys prf

-- Completeness: any node of rank r contained in nodes G appears in same-rank-nodes G r.
same-rank-complete :
  ∀ {G : DriftGraph} {r : ℕ} {n : Node} →
  n ∈ nodes G → nodeId n ≡ r → n ∈ same-rank-nodes G r
same-rank-complete {G} {r} {n} n∈ eq = insert (nodes G) n∈
  where
    p : Node → Bool
    p node = rank-match (nodeId node) r

    insert : ∀ (xs : List Node) → n ∈ xs → n ∈ bool-filter p xs
    insert [] ()
    insert (y ∷ ys) here with p y | rank-match-true eq
    ... | true  | _        = here
    ... | false | py≡true  =
      ⊥-elim (false≠true (trans (sym refl) py≡true))
    insert (y ∷ ys) (there prf) with p y
    ... | true  = there (insert ys prf)
    ... | false = insert ys prf