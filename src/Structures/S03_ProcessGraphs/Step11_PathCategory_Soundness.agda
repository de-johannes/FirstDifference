{-# OPTIONS --safe #-}

-- Soundness for Step 11 (PathCategory):
-- Any path is either the identity (u ≡ v) OR exhibits reachability u ⇝ v.

module Structures.S03_ProcessGraphs.Step11_PathCategory_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Structures.S03_ProcessGraphs.Step10_DriftGraph as DG
  using (DriftGraph; NodeId; _—→_within_; _can-reach_within_; direct; compose)

open import Structures.S03_ProcessGraphs.Step11_PathCategory as PC
  using (Path; refl-path; _∷-path_; _++-path_)

------------------------------------------------------------------------
-- Main lemma: a path is either trivial (identity) or yields reachability
------------------------------------------------------------------------

path⇒reach⊎eq : ∀ {G u v} → PC.Path G u v →
                 (u DG.can-reach v within G) ⊎ (u ≡ v)
path⇒reach⊎eq PC.refl-path = inj₂ refl
path⇒reach⊎eq (e PC.∷-path p) with path⇒reach⊎eq p
... | inj₁ v⇝w = inj₁ (DG.compose (DG.direct e) v⇝w)
... | inj₂ refl = inj₁ (DG.direct e)

------------------------------------------------------------------------
-- Convenience: any non-empty path (edge cons) gives reachability
------------------------------------------------------------------------

edgePath⇒reach : ∀ {G u v w} →
                 (e : u DG.—→ v within G) → (p : PC.Path G v w) →
                 u DG.can-reach w within G
edgePath⇒reach e p with path⇒reach⊎eq p
... | inj₁ v⇝w = DG.compose (DG.direct e) v⇝w
... | inj₂ refl = DG.direct e