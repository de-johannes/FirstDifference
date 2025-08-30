{-# OPTIONS --safe #-}

-- Step 14: Spatial structure – Soundness & Completeness of the rank filter
-- We prove that same-rank-nodes picks exactly the nodes whose nodeId = rank.

module Structures.S03_ProcessGraphs.Step14_SpatialStructure_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
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
  using (bool-filter; same-rank-nodes)

------------------------------------------------------------------------
-- Boolean-filter lemmas specialized to Node-membership
------------------------------------------------------------------------

filter-sound-Node :
  ∀ (p : Node → Bool) (xs : List Node) {n : Node} →
  n ∈ bool-filter p xs → p n ≡ true
filter-sound-Node p [] ()
filter-sound-Node p (y ∷ ys) {n} prf with p y
... | true  with prf
...   | here        = refl
...   | there prf'  = filter-sound-Node p ys prf'
... | false = filter-sound-Node p ys prf

-- If n ∈ xs and p n ≡ true then n ∈ bool-filter p xs.
filter-complete-Node :
  ∀ (p : Node → Bool) (xs : List Node) {n : Node} →
  n ∈ xs → p n ≡ true → n ∈ bool-filter p xs
filter-complete-Node p [] () _
filter-complete-Node p (y ∷ ys) {n} here pn with p y
... | true  rewrite pn = here
... | false rewrite pn = ⊥-elim (λ ())  -- impossible since pn ≡ true
filter-complete-Node p (y ∷ ys) {n} (there prf) pn with p y
... | true  = there (filter-complete-Node p ys prf pn)
... | false = filter-complete-Node p ys prf pn

------------------------------------------------------------------------
-- Convert decidable equality on ℕ to our project Bool
------------------------------------------------------------------------

eqᵇ : ℕ → ℕ → Bool
eqᵇ m r with m ≟ r
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Specialization to same-rank-nodes
------------------------------------------------------------------------

-- Soundness: every member filtered by same-rank-nodes has matching rank.
same-rank-sound :
  ∀ {G : DriftGraph} {r : ℕ} {n : Node} →
  n ∈ same-rank-nodes G r → nodeId n ≡ r
same-rank-sound {G} {r} {n} m
  with nodeId n ≟ r | filter-sound-Node (λ node → eqᵇ (nodeId node) r) (nodes G) m
... | yes eq | _    = eq
... | no  _  | ()   -- impossible: would force false ≡ true

-- If m ≡ r then the decidable test (m ≟ r) yields true under our Bool
dec-eq-true : ∀ (m r : ℕ) → m ≡ r → eqᵇ m r ≡ true
dec-eq-true .r r refl with r ≟ r
... | yes _      = refl
... | no contra  = ⊥-elim (contra refl)

-- Completeness: any node of rank r contained in nodes G appears in same-rank-nodes G r.
same-rank-complete :
  ∀ {G : DriftGraph} {r : ℕ} {n : Node} →
  n ∈ nodes G → nodeId n ≡ r → n ∈ same-rank-nodes G r
same-rank-complete {G} {r} {n} n∈ eq =
  filter-complete-Node
    (λ node → eqᵇ (nodeId node) r)
    (nodes G)
    n∈
    dec-eq-true (nodeId n) r eq