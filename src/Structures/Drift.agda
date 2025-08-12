module Structures.Drift where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)  -- Added _≤_
open import Data.Nat.Properties using (≤-refl; ≤-step)  -- Added these imports
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Vec as Vec using (Vec; []; _∷_; zipWith)

------------------------------------------------------------------------
-- Distinctions as fixed-length Bool vectors
------------------------------------------------------------------------

record Dist (n : ℕ) : Set where
  constructor mkDist
  field poles : Vec Bool n
open Dist public

-- Boolean AND for drift composition (parent conjunction)
drift : ∀ {n} → Dist n → Dist n → Dist n
drift d1 d2 = mkDist (zipWith _∧_ (poles d1) (poles d2))

------------------------------------------------------------------------
-- History = sequence of distinction events with temporal ordering
------------------------------------------------------------------------

History : ℕ → Set
History n = List (Dist n)

-- Boolean equality for distinctions
eqBool : Bool → Bool → Bool
eqBool true  true  = true
eqBool false false = true
eqBool _     _     = false

eqVec : ∀ {n} → Vec Bool n → Vec Bool n → Bool
eqVec {zero}  []       []       = true
eqVec {suc n} (x ∷ xs) (y ∷ ys) with eqBool x y
... | true  = eqVec xs ys
... | false = false

eqDist : ∀ {n} → Dist n → Dist n → Bool
eqDist d₁ d₂ = eqVec (poles d₁) (poles d₂)

-- Check if distinction appears in history
anyEq : ∀ {n} → Dist n → History n → Bool
anyEq _ []       = false
anyEq d (x ∷ xs) with eqDist d x
... | true  = true
... | false = anyEq d xs

-- Generate all pairwise drift combinations from history
allDriftCombinations : ∀ {n} → History n → List (Dist n)
allDriftCombinations []       = []
allDriftCombinations (x ∷ xs) =
  let rec = allDriftCombinations xs
  in  x ∷ rec ++ map (λ d → drift x d) rec

------------------------------------------------------------------------
-- Irreducibility: key filter for semantic time
------------------------------------------------------------------------

-- A distinction is irreducible if it's not derivable from past drift operations
irreducible? : ∀ {n} → Dist n → History n → Bool
irreducible? δ prev = not (anyEq δ (allDriftCombinations prev))

-- Semantic Time: counts only irreducible distinction events
T : ∀ {n} → History n → ℕ
T [] = zero
T (δ ∷ prev) with irreducible? δ prev
... | true  = suc (T prev)    -- Irreducible event: time advances
... | false = T prev          -- Reducible event: no time advancement

-- Every history step either advances time or stays constant
ArrowOfTime :
  ∀ {n} (δ : Dist n) (prev : History n) →
  (T (δ ∷ prev) ≡ T prev) ⊎ (T (δ ∷ prev) ≡ suc (T prev))
ArrowOfTime δ prev with irreducible? δ prev
... | true  = inj₂ refl  -- Time arrow advances
... | false = inj₁ refl  -- Time stays constant

-- Helper: reflexivity from equality
≤-refl-from-eq : ∀ {m n} → m ≡ n → m ≤ n
≤-refl-from-eq refl = ≤-refl

-- Semantic time is monotonic: never decreases
T-monotonic : ∀ {n} (h : History n) (d : Dist n) → T h ≤ T (d ∷ h)
T-monotonic h d with ArrowOfTime d h
... | inj₁ eq = ≤-refl-from-eq (sym eq)
... | inj₂ eq = ≤-step ≤-refl
