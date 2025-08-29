{-# OPTIONS --safe #-}

-- | Step 05: Semilattice — Soundness Layer
-- |
-- | Purpose:
-- |   Provide soundness certificates (sound-…) for the semilattice
-- |   instance on distinction vectors, re-exporting the laws of
-- |   MeetSemilattice⊥ and JoinSemilattice⊤.
-- |
-- | Guarantee:
-- |   No new proofs; only aliasing of verified fields.

module Structures.S02_OrderCategories.Step05_Semilattice_Soundness where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Core ops
open import Structures.S01_BooleanCore.Step02_VectorOperations using (Dist)

-- Import the semilattice packaging
open import Structures.S02_OrderCategories.Step05_Semilattice

------------------------------------------------------------------------
-- Meet-semilattice soundness (drift, all-false)
------------------------------------------------------------------------

sound-meetSemilattice⊥ : ∀ {n} → MeetSemilattice⊥ n
sound-meetSemilattice⊥ = meetSemilatticeᵈ

sound-⋀-assoc   : ∀ {n} (x y z : Dist n) → (MeetSemilattice⊥._⋀_ (sound-meetSemilattice⊥ {n})) ((MeetSemilattice⊥._⋀_ (sound-meetSemilattice⊥ {n})) x y) z
                  ≡ (MeetSemilattice⊥._⋀_ (sound-meetSemilattice⊥ {n})) x ((MeetSemilattice⊥._⋀_ (sound-meetSemilattice⊥ {n})) y z)
sound-⋀-assoc = MeetSemilattice⊥.assoc (sound-meetSemilattice⊥ _)

sound-⋀-comm    : ∀ {n} (x y : Dist n) → (MeetSemilattice⊥._⋀_ (sound-meetSemilattice⊥ {n})) x y ≡ (MeetSemilattice⊥._⋀_ (sound-meetSemilattice⊥ {n})) y x
sound-⋀-comm = MeetSemilattice⊥.comm (sound-meetSemilattice⊥ _)

sound-⋀-idemp   : ∀ {n} (x : Dist n) → (MeetSemilattice⊥._⋀_ (sound-meetSemilattice⊥ {n})) x x ≡ x
sound-⋀-idemp = MeetSemilattice⊥.idemp (sound-meetSemilattice⊥ _)

------------------------------------------------------------------------
-- Join-semilattice soundness (join, all-true)
------------------------------------------------------------------------

sound-joinSemilattice⊤ : ∀ {n} → JoinSemilattice⊤ n
sound-joinSemilattice⊤ = joinSemilatticeᵈ

sound-⋁-assoc  : ∀ {n} (x y z : Dist n) → (JoinSemilattice⊤._⋁_ (sound-joinSemilattice⊤ {n})) ((JoinSemilattice⊤._⋁_ (sound-joinSemilattice⊤ {n})) x y) z
                 ≡ (JoinSemilattice⊤._⋁_ (sound-joinSemilattice⊤ {n})) x ((JoinSemilattice⊤._⋁_ (sound-joinSemilattice⊤ {n})) y z)
sound-⋁-assoc = JoinSemilattice⊤.assoc (sound-joinSemilattice⊤ _)

sound-⋁-comm   : ∀ {n} (x y : Dist n) → (JoinSemilattice⊤._⋁_ (sound-joinSemilattice⊤ {n})) x y ≡ (JoinSemilattice⊤._⋁_ (sound-joinSemilattice⊤ {n})) y x
sound-⋁-comm = JoinSemilattice⊤.comm (sound-joinSemilattice⊤ _)

sound-⋁-idemp  : ∀ {n} (x : Dist n) → (JoinSemilattice⊤._⋁_ (sound-joinSemilattice⊤ {n})) x x ≡ x
sound-⋁-idemp = JoinSemilattice⊤.idemp (sound-joinSemilattice⊤ _)