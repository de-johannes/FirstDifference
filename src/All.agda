module All where

------------------------------------------------------------------------
-- Core: Foundational principles
------------------------------------------------------------------------

-- The Token Principle and irrefutability theorems
open import Core.TokenPrinciple public
open import Core.Irrefutable public

------------------------------------------------------------------------
-- Structures
------------------------------------------------------------------------

-- (A) Boolean Core — Distinction → Boolean algebra (constructive)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation                             public
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Soundness                   public
open import Structures.S01_BooleanCore.Step02_VectorOperations                              public
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness                    public
open import Structures.Step3_AlgebraLaws       public

-- (B) Order & Categories — Drift order and categorical scaffolding
open import Structures.Step4_PartialOrder      public
open import Structures.Step5_CategoryStructure public

-- (C) Time Emergence — Semantic time as a functor on sequences
open import Structures.Step6_SemanticTimeFunctor public

-- (D) Process Graphs & Temporal Functors — Paths, Cuts, and evolution
open import Structures.Step7_DriftGraph        public
open import Structures.Step8_PathCategory      public
open import Structures.Step8_CutCategory       public
open import Structures.Step8_TemporalFunctor   public

-- (E) Space from Simultaneity — Spatial slices from equal-rank nodes
open import Structures.Step9_SpatialStructure  public

-- (F) FoldMap & Dimensionality — Projection to data; Rank-3 proof
open import Structures.Step10_FoldMap          public
open import Structures.Step11_Rank3            public
open import Structures.Step12_Rank3_Soundness  public

-- (G) Operadic Cohesion — Composable operations on Cells/Nodes
open import Structures.Step13_OperadicCohesion public

------------------------------------------------------------------------
-- Physics
------------------------------------------------------------------------

open import Physics.Step14_EFI_Core public


------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

-- import Examples.Demo                     as ExDemo
-- import Examples.DriftSim                 as ExDriftSim
-- import Examples.DriftWithTPProof         as ExDriftTP
import Examples.EFI_FoldMap_SmokeTest    as ExEfiSmoke
