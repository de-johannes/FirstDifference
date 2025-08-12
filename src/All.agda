module All where

-- Public surface: only the safe, axioms-free core and examples.
open import Core.TokenPrinciple public
open import Core.Irrefutable   public
open import Core.Demo          public

open import Structures.CutCat  public
open import Structures.Drift   public
open import Structures.DistOpOperad public
open import Structures.RelOperad public
open import Structures.Functors public renaming (plus to plusF)

open import Examples.DriftSim  public
open import Examples.CutCatDistOp public
