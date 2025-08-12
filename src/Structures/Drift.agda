{-# OPTIONS --safe #-}

-- | The core drift algebra: how distinctions compose and evolve
-- | This module defines the fundamental operations on distinctions
-- | and establishes semantic time through irreducibility
module Structures.Drift where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec as Vec using (Vec; []; _∷_; zipWith)
open import Structures.CutCat using (_≤_; z≤n; s≤s; refl≤)

------------------------------------------------------------------------
-- Distinctions as Boolean vectors
------------------------------------------------------------------------

-- | A distinction of dimension n: a fixed-length vector of Boolean poles
-- | Each Boolean represents a polar choice (marked/unmarked)
record Dist (n : ℕ) : Set where
  constructor mkDist
  field poles : Vec Bool n
open Dist public

-- | Drift operation: Boolean AND composition of distinctions
-- | This models "both conditions must hold" - the intersection of constraints
drift : ∀ {n} → Dist n → Dist n → Dist n
drift d1 d2 = mkDist (zipWith _∧_ (poles d1) (poles d2))

------------------------------------------------------------------------
-- Temporal History and Evolution
------------------------------------------------------------------------

-- | History: sequence of distinction events over time
-- | Each element represents a distinction that occurred
History : ℕ → Set
History n = List (Dist n)

-- | Boolean equality for individual Boolean values
eqBool : Bool → Bool → Bool
eqBool true  true  = true
eqBool false false = true
eqBool _     _     = false

-- | Vector equality: component-wise Boolean comparison
eqVec : ∀ {n} → Vec Bool n → Vec Bool n → Bool
eqVec {zero}  []       []       = true
eqVec {suc n} (x ∷ xs) (y ∷ ys) with eqBool x y
... | true  = eqVec xs ys
... | false = false

-- | Distinction equality: wrapper for vector equality
eqDist : ∀ {n} → Dist n → Dist n → Bool
eqDist d₁ d₂ = eqVec (poles d₁) (poles d₂)

-- | Check if a distinction appears anywhere in history
anyEq : ∀ {n} → Dist n → History n → Bool
anyEq _ []       = false
anyEq d (x ∷ xs) with eqDist d x
... | true  = true
... | false = anyEq d xs

-- | Generate all possible drift combinations from history
-- | This creates all distinctions derivable through drift operations
allDriftCombinations : ∀ {n} → History n → List (Dist n)
allDriftCombinations []       = []
allDriftCombinations (x ∷ xs) =
  let rec = allDriftCombinations xs
  in  x ∷ rec ++ map (λ d → drift x d) rec

------------------------------------------------------------------------
-- Irreducibility: The key to semantic time
------------------------------------------------------------------------

-- | Irreducibility test: A distinction is irreducible if it cannot
-- | be derived from previous distinctions through drift operations
-- | This is the crucial filter for what "advances semantic time"
irreducible? : ∀ {n} → Dist n → History n → Bool
irreducible? δ prev = not (anyEq δ (allDriftCombinations prev))

-- | Semantic Time function: counts only irreducible distinction events
-- | This gives us a measure of "genuine temporal advancement"
T : ∀ {n} → History n → ℕ
T [] = zero
T (δ ∷ prev) with irreducible? δ prev
... | true  = suc (T prev)    -- Irreducible: time advances by 1
... | false = T prev          -- Reducible: no time advancement

-- | The Arrow of Time theorem: time either stays constant or advances by 1
-- | This captures the discrete, monotonic nature of semantic time
ArrowOfTime : ∀ {n} (δ : Dist n) (prev : History n) →
  (T (δ ∷ prev) ≡ T prev) ⊎ (T (δ ∷ prev) ≡ suc (T prev))
ArrowOfTime δ prev with irreducible? δ prev
... | true  = inj₂ refl  -- Time advances (right injection)
... | false = inj₁ refl  -- Time stays constant (left injection)

-- | Helper lemma: n ≤ suc n using CutCat constructors
n≤suc-n : ∀ n → n ≤ suc n
n≤suc-n zero    = z≤n
n≤suc-n (suc n) = s≤s (n≤suc-n n)

-- | Semantic time is monotonic: never decreases with new events
-- | This establishes the fundamental temporal ordering property
T-monotonic : ∀ {n} (h : History n) (d : Dist n) → T h ≤ T (d ∷ h)
T-monotonic h d with irreducible? d h
... | true  = n≤suc-n (T h)  -- T advances by 1, so T h ≤ suc (T h)
... | false = refl≤ (T h)    -- T stays same, so T h ≤ T h
