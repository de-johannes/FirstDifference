module All where

------------------------------------------------------------------------
-- Core: Foundational principles (axioms-free, safe)
------------------------------------------------------------------------

-- The Token Principle and irrefutability theorems
open import Core.TokenPrinciple public
open import Core.Irrefutable public

------------------------------------------------------------------------

-- Enhanced Structures --
open import Structures.Step1_BooleanFoundation public
open import Structures.Step2_VectorOperations public
open import Structures.Step3_AlgebraLaws public
open import Structures.Step4_PartialOrder public
open import Structures.Step5_CategoryStructure public
open import Structures.Step6_SemanticTimeFunctor public
open import Structures.Step7_DriftGraph public
open import Structures.Step8_PathCategory public
open import Structures.Step8_CutCategory public
open import Structures.Step8_TemporalFunctor public
open import Structures.Step9_SpatialStructure public
open import Structures.Step10_FoldMap public
open import Structures.Step11_Rank3 public
open import Structures.Step12_Rank3_Soundness public

------------------------------------------------------------------------
-- Examples and demonstrations
------------------------------------------------------------------------

import Examples.DriftWithTPProof as DriftTP
-- open import Core.Demo          public
-- open import Examples.DriftSim  public
