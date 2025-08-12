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

-- Conceptual bridges (key for coherence)
open import Structures.DriftToCut public
open import Structures.DriftToOperad public

-- Categorical backbone
open import Structures.CutCat public
open import Structures.DistOpOperad public

-- The semantic functor (replaces old Functors)
open import Structures.SemanticFunctor public

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
