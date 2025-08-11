module Examples.DriftSim where

-- Purpose
-- -------
-- This is a *standalone* micro-simulation that mirrors the intuition behind “drift”:
-- combine two distinctions and see whether something genuinely “new” appears.
--
-- Design choices (so CI stays green and we avoid name clashes):
-- • We use an example-only type `EDist` instead of the real `Structures.Drift.Dist`.
-- • Example drift `edrift` is Boolean AND on a one-bit “mark”. That models co-dependency:
--   a child is active only if both parents are active.
-- • We tag each step as New vs Stagnant to count “innovations”.
--
-- This file deliberately does *not* import your real structures. It’s a didactic, runnable
-- toy that exercises the intuition and gives the CI something nontrivial to check.

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Sum  using (_⊎_; inj₁; inj₂)
open import Data.Nat  using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- 1) Example distinction and example drift
------------------------------------------------------------------------

-- One-bit distinction for the example world
data EDist : Set where
  ebit : Bool → EDist

-- Example drift = Boolean AND on the underlying bit
-- Read: a child is present iff both parents are present (co-dependency)
edrift : EDist → EDist → EDist
edrift (ebit b₁) (ebit b₂) = ebit (b₁ ∧ b₂)

------------------------------------------------------------------------
-- 2) Detect “innovation” vs “stagnation”
------------------------------------------------------------------------

data StepTag : Set where
  New Stagnant : StepTag

-- A single step: either marks a New event (innovation) or returns the stagnant state
-- New iff edrift returns the marked pole (true); otherwise we expose the stagnant child
step : EDist → EDist → (StepTag ⊎ EDist)
step d₁ d₂ with edrift d₁ d₂
... | ebit true  = inj₁ New
... | ebit false = inj₂ (ebit false)

-- Boolean tester (sometimes handier than the ⊎ variant)
innovates? : EDist → EDist → Bool
innovates? d₁ d₂ with edrift d₁ d₂
... | ebit true  = true
... | ebit false = false

------------------------------------------------------------------------
-- 3) Tiny aggregator: count how many “New” events occur in a list of parent pairs
------------------------------------------------------------------------

-- We fold a list of parent pairs and increment on New.
countNew : List (EDist × EDist) → ℕ
countNew =
  foldr
    (λ p acc →
       let d₁ = proj₁ p
           d₂ = proj₂ p
       in  helper d₁ d₂ acc)
    zero
  where
    helper : EDist → EDist → ℕ → ℕ
    helper d₁ d₂ acc with innovates? d₁ d₂
    ... | true  = suc acc
    ... | false = acc

------------------------------------------------------------------------
-- 4) Sanity checks (definitional equalities so CI actually proves something)
------------------------------------------------------------------------

-- AND(true, true) → New
step-true-true : step (ebit true) (ebit true) ≡ inj₁ New
step-true-true = refl

-- AND(true, false) → Stagnant with false
step-true-false : step (ebit true) (ebit false) ≡ inj₂ (ebit false)
step-true-false = refl

-- A small scenario: [(1,1), (1,0), (0,1)] has exactly one innovation
exScenario : List (EDist × EDist)
exScenario =
  (ebit true  , ebit true)  ∷
  (ebit true  , ebit false) ∷
  (ebit false , ebit true)  ∷
  []

exScenario-count : countNew exScenario ≡ suc zero
exScenario-count = refl
