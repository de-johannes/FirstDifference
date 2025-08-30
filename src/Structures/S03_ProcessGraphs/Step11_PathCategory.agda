-- src/Structures/S03_ProcessGraphs/Step11_PathCategory.agda
{-# OPTIONS --safe #-}

-- | Step 11: Path Category
-- |
-- | Build the reachability category R(G) from a DriftGraph:
-- | • Objects: Node identifiers
-- | • Morphisms: Paths (sequences of edges)
-- | • Laws: Identity and associativity, proven by induction
module Structures.S03_ProcessGraphs.Step11_PathCategory where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_)

-- DriftGraph from Step 10
open import Structures.S03_ProcessGraphs.Step10_DriftGraph as DG

------------------------------------------------------------------------
-- 1. Path definition
------------------------------------------------------------------------

data Path (G : DG.DriftGraph) : DG.NodeId → DG.NodeId → Set where
  refl-path : ∀ {u} → Path G u u
  _∷-path_  : ∀ {u v w} → (e : u DG.—→ v within G) → Path G v w → Path G u w

infixr 5 _∷-path_

------------------------------------------------------------------------
-- 2. Composition
------------------------------------------------------------------------

_++-path_ : ∀ {G u v w} → Path G u v → Path G v w → Path G u w
refl-path      ++-path q = q
(e ∷-path p) ++-path q = e ∷-path (p ++-path q)

infixr 5 _++-path_

------------------------------------------------------------------------
-- 3. Category laws
------------------------------------------------------------------------

path-assoc : ∀ {G a b c d} (p : Path G a b) (q : Path G b c) (r : Path G c d) →
             (p ++-path q) ++-path r ≡ p ++-path (q ++-path r)
path-assoc refl-path      q r = refl
path-assoc (e ∷-path p) q r = cong (e ∷-path_) (path-assoc p q r)

path-idˡ : ∀ {G u v} (p : Path G u v) → refl-path ++-path p ≡ p
path-idˡ p = refl

path-idʳ : ∀ {G u v} (p : Path G u v) → p ++-path refl-path ≡ p
path-idʳ refl-path     = refl
path-idʳ (e ∷-path p) = cong (e ∷-path_) (path-idʳ p)

------------------------------------------------------------------------
-- 4. Abstract category record
------------------------------------------------------------------------

record Category (Obj : Set) (Hom : Obj → Obj → Set) : Set₁ where
  field
    id    : ∀ A → Hom A A
    _∘_   : ∀ {A B C} → Hom A B → Hom B C → Hom A C
    idˡ   : ∀ {A B} (f : Hom A B) → (id A) ∘ f ≡ f
    idʳ   : ∀ {A B} (f : Hom A B) → f ∘ (id B) ≡ f
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D) →
            (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

------------------------------------------------------------------------
-- 5. Reachability category R(G)
------------------------------------------------------------------------

DriftPathCategory : (G : DG.DriftGraph) → Category (DG.NodeId) (Path G)
DriftPathCategory G = record
  { id    = λ A → refl-path
  ; _∘_   = _++-path_
  ; idˡ   = path-idˡ
  ; idʳ   = path-idʳ
  ; assoc = path-assoc
  }