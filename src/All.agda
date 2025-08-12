module All where

------------------------------------------------------------------------
-- Core: Foundational principles (axioms-free, safe)
------------------------------------------------------------------------

-- The Token Principle and irrefutability theorems
open import Core.TokenPrinciple public
open import Core.Irrefutable   public

------------------------------------------------------------------------
-- Structures: The complete conceptual chain  
-- Possibility → D₀ → Drift → CutCat → DistOp → Arithmetic
------------------------------------------------------------------------

-- Enhanced drift with semantic time
open import Structures.Drift public
open import Structures.Step1_BooleanFoundation public

------------------------------------------------------------------------
-- Integration: Complete foundational chain
------------------------------------------------------------------------

-- Shows the full conceptual pathway
open import Integration.DriftToMath public

------------------------------------------------------------------------
-- Optional: Examples and demonstrations
------------------------------------------------------------------------

-- Keep existing demos if they still compile
-- open import Core.Demo          public
-- open import Structures.RelOperad public  
-- open import Examples.DriftSim  public
-- open import Examples.CutCatDistOp public
