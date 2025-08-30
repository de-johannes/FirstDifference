{-# OPTIONS --safe #-}

-- Step 14: Spatial structure – Soundness & Completeness of the rank filter
-- We prove that same-rank-nodes picks exactly the nodes whose nodeId = rank.

module Structures.S03_ProcessGraphs.Step14_SpatialStructure_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
-- Generic Boolean-filter lemmas (for list membership)
------------------------------------------------------------------------

-- If x is in (bool-filter p xs) then p x ≡ true.
filter-sound :
  ∀ {A : Set} {x : A} (p : A → _) (xs : List A) →
  x ∈ bool-filter p xs → p x ≡ true
filter-sound p [] ()
filter-sound p (x ∷ xs) with p x
... | true  = λ { here → refl ; there m → filter-sound p xs m }
... | false = λ m → filter-sound p xs m

-- If x ∈ xs and p x ≡ true then x ∈ bool-filter p xs.
filter-complete :
  ∀ {A : Set} {x : A} (p : A → _) (xs : List A) →
  x ∈ xs → p x ≡ true → x ∈ bool-filter p xs
filter-complete p [] () _
filter-complete p (x ∷ xs) here px rewrite px = here
filter-complete p (y ∷ xs) (there m) px with p y
... | true  = there (filter-complete p xs m px)
... | false = filter-complete p xs m px

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
  with nodeId n ≟ r | filter-sound (λ node → eqᵇ (nodeId node) r) (nodes G) m
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
  filter-complete
    (λ node → eqᵇ (nodeId node) r)
    (nodes G)
    n∈
    dec-eq-true (nodeId n) r eq