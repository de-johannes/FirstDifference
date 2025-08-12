module All where

------------------------------------------------------------------------
-- Core: Foundational principles (axioms-free, safe)
------------------------------------------------------------------------

-- The Token Principle and irrefutability theorems
open import Core.TokenPrinciple public
open import Core.Irrefutable   public

------------------------------------------------------------------------

-- Enhanced Structures --
open import Structures.Step1_BooleanFoundation public
open import Structures.Step2_VectorOperations public
open import Structures.Step3_AlgebraLaws public
open import Structures.Step4_PartialOrder public
open import Structures.Step5_CategoryStructure public
open import Structures.Step6_SemanticTimeFunctor public

------------------------------------------------------------------------
-- Optional: Examples and demonstrations
------------------------------------------------------------------------

-- Keep existing demos if they still compile
-- open import Core.Demo          public
-- open import Structures.RelOperad public  
-- open import Examples.DriftSim  public
-- open import Examples.CutCatDistOp public
