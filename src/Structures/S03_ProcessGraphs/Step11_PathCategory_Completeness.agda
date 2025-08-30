{-# OPTIONS --safe #-}

-- Completeness for Step 11 (PathCategory):
-- Any reachability proof u ⇝ v induces a (non-empty) path from u to v.

module Structures.S03_ProcessGraphs.Step11_PathCategory_Completeness where

open import Structures.S03_ProcessGraphs.Step10_DriftGraph as DG
  using (DriftGraph; NodeId; _—→_within_; _can-reach_within_; direct; compose)

open import Structures.S03_ProcessGraphs.Step11_PathCategory as PC
  using (Path; refl-path; _∷-path_; _++-path_)

------------------------------------------------------------------------
-- Reachability ⇒ (non-empty) path
------------------------------------------------------------------------

reach⇒path : ∀ {G u v} → u DG.can-reach v within G → PC.Path G u v
reach⇒path (DG.direct e)     = e PC.∷-path PC.refl-path
reach⇒path (DG.compose p q)  = PC._++-path_ (reach⇒path p) (reach⇒path q)