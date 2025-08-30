module All where

------------------------------------------------------------------------
-- Core: Foundational principles
------------------------------------------------------------------------

-- The Token Principle and irrefutability theorems
open import Core.TokenPrinciple                                                             public
open import Core.Irrefutable                                                                public


------------------------------------------------------------------------
-- Structures
------------------------------------------------------------------------

-- (S01_BooleanCore) Boolean Core — Distinction → Boolean algebra (constructive)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation                             public
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Soundness                   public
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Completeness                public
open import Structures.S01_BooleanCore.Step02_VectorOperations                              public
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness                    public
open import Structures.S01_BooleanCore.Step03_AlgebraLaws                                   public
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness                         public

-- (S02_OrderCategories) Order & Categories — Drift order and categorical scaffolding
open import Structures.S02_OrderCategories.Step04_PartialOrder                              public
open import Structures.S02_OrderCategories.Step04_PartialOrder_Soundness                    public
open import Structures.S02_OrderCategories.Step04_PartialOrder_Completeness                 public
open import Structures.S02_OrderCategories.Step05_Semilattice                               public
open import Structures.S02_OrderCategories.Step05_Semilattice_Soundness                     public
open import Structures.S02_OrderCategories.Step06_BoundedLattice                            public
open import Structures.S02_OrderCategories.Step07_BooleanAlgebra                            public
open import Structures.S02_OrderCategories.Step07_BooleanAlgebra_Soundness                  public
open import Structures.S02_OrderCategories.Step08_CategoryStructure                         public
open import Structures.S02_OrderCategories.Step09_SemanticTimeFunctor                       public


-- (S03_ProcessGraphs) Process Graphs & Temporal Functors — Paths, Cuts, and evolution
open import Structures.S03_ProcessGraphs.Step10_DriftGraph                                  public
open import Structures.S03_ProcessGraphs.Step11_PathCategory                                public
open import Structures.S03_ProcessGraphs.Step11_PathCategory_Soundness                      public
open import Structures.S03_ProcessGraphs.Step11_PathCategory_Completeness                   public
open import Structures.S03_ProcessGraphs.Step12_CutCategory                                 public
open import Structures.S03_ProcessGraphs.Step13_PathToCutFunctor                            public
open import Structures.S03_ProcessGraphs.Step14_SpatialStructure                            public
open import Structures.S03_ProcessGraphs.Step14_SpatialStructure_Soundness                  public


-- (S04_Projection) FoldMap & Dimensionality — Projection to data; Rank-3 proof
open import Structures.S04_Projection.Step15_FoldMap                                        public
open import Structures.S04_Projection.Step15_FoldMap_Soundness                              public
open import Structures.S04_Projection.Step16_Rank3                                          public
open import Structures.S04_Projection.Step16_Rank3_Soundness                                public
open import Structures.S04_Projection.Step17_OperadicCohesion                               public


------------------------------------------------------------------------
-- Physics
------------------------------------------------------------------------

open import Physics.Step01_EFI_Core                                                         public


------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

-- import Examples.Demo                     as ExDemo
-- import Examples.DriftSim                 as ExDriftSim
-- import Examples.DriftWithTPProof         as ExDriftTP
import Examples.EFI_FoldMap_SmokeTest       as ExEfiSmoke
