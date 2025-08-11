module Examples.DriftSim where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Data.Vec as Vec
open Vec using (Vec; []; _∷_)

open import Structures.Drift

-- A tiny 3-bit world
dA : Dist 3
dA = mkDist (true  ∷ false ∷ true  ∷ [])

dB : Dist 3
dB = mkDist (true  ∷ true  ∷ false ∷ [])

dC : Dist 3
dC = mkDist (false ∷ true  ∷ true  ∷ [])

-- A toy history
hist : List (Dist 3)
hist = dA ∷ dB ∷ dC ∷ []

-- A computed sample value (Agda normalises this)
sampleT : ℕ
sampleT = T hist

-- Sanity check: ArrowOfTime yields one of the two exact equalities, by case.
check-step₁ : (T (dA ∷ []) ≡ T []) ⊎ (T (dA ∷ []) ≡ suc (T []))
check-step₁ = ArrowOfTime dA []

-- You can add more examples here; they will type-check and normalise.
