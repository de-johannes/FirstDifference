module Structures.Drift where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Use qualified Vec to avoid clashes with List.
import Data.Vec as Vec
open Vec using (Vec; []; _∷_; zipWith)

------------------------------------------------------------------------
-- Distinctions as fixed-length Bool vectors
------------------------------------------------------------------------

record Dist (n : ℕ) : Set where
  constructor mkDist
  field poles : Vec Bool n
open Dist public

-- Boolean AND for drift composition
drift : ∀ {n} → Dist n → Dist n → Dist n
drift d1 d2 = mkDist (zipWith _∧_ (poles d1) (poles d2))

------------------------------------------------------------------------
-- Helpers: Bool/Vec equality, membership
------------------------------------------------------------------------

not : Bool → Bool
not true  = false
not false = true

eqBool : Bool → Bool → Bool
eqBool true  true  = true
eqBool false false = true
eqBool _     _     = false

eqVec : ∀ {n} → Vec Bool n → Vec Bool n → Bool
eqVec {n = zero}  []       []       = true
eqVec {n = suc n} (x ∷ xs) (y ∷ ys) with eqBool x y
... | true  = eqVec xs ys
... | false = false

eqDist : ∀ {n} → Dist n → Dist n → Bool
eqDist d₁ d₂ = eqVec (poles d₁) (poles d₂)

anyEq : ∀ {n} → Dist n → List (Dist n) → Bool
anyEq _ []       = false
anyEq d (x ∷ xs) with eqDist d x
... | true  = true
... | false = anyEq d xs

------------------------------------------------------------------------
-- Generate all pairwise conjunctions against the past
------------------------------------------------------------------------

allConjunctions : ∀ {n} → List (Dist n) → List (Dist n)
allConjunctions []       = []
allConjunctions (x ∷ xs) =
  let rec = allConjunctions xs
  in  x ∷ rec ++ map (λ d → drift x d) rec

------------------------------------------------------------------------
-- Irreducibility (computational, boolean)
------------------------------------------------------------------------

irreducible? : ∀ {n} → Dist n → List (Dist n) → Bool
irreducible? δ prev = not (anyEq δ (allConjunctions prev))

------------------------------------------------------------------------
-- "Semantic time" counter based on irreducibility?
------------------------------------------------------------------------

T : ∀ {n} → List (Dist n) → ℕ
T [] = zero
T (δ ∷ prev) with irreducible? δ prev
... | true  = suc (T prev)
... | false = T prev

ArrowOfTime :
  ∀ {n} (δ : Dist n) (prev : List (Dist n)) →
  (T (δ ∷ prev) ≡ T prev) ⊎ (T (δ ∷ prev) ≡ suc (T prev))
ArrowOfTime δ prev with irreducible? δ prev
... | true  = inj₂ refl
... | false = inj₁ refl
