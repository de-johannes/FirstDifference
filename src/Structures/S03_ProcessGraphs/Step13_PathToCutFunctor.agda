-- src/Structures/S03_ProcessGraphs/Step13_PathToCutFunctor.agda
{-# OPTIONS --safe #-}

-- | Step 13: Functor from Path Category to Cut Category
-- |
-- | For any DriftGraph G:
-- |   R(G)  --(PathToCut)-->  CutCat
-- | Objects: Node identifiers (ℕ).
-- | Morphisms: Paths map to ≤-proofs via temporal monotonicity.
module Structures.S03_ProcessGraphs.Step13_PathToCutFunctor where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)

-- Source/target categories and path ops
open import Structures.S03_ProcessGraphs.Step11_PathCategory
  as PC using (Category; Path; _++-path_; DriftPathCategory)

open import Structures.S03_ProcessGraphs.Step12_CutCategory
  as Cut using (CutCat; ≤-idˡ; ≤-assoc; <⇒≤)

-- Graph structure and edge monotonicity
open import Structures.S03_ProcessGraphs.Step10_DriftGraph
  as DG using (DriftGraph; NodeId; _—→_within_; edge-increases-time)

------------------------------------------------------------------------
-- A minimal functor record between two categories
------------------------------------------------------------------------

record Functor
  (ObjC : Set) (HomC : ObjC → ObjC → Set) (C : Category ObjC HomC)
  (ObjD : Set) (HomD : ObjD → ObjD → Set) (D : Category ObjD HomD)
  : Set₁ where
  field
    F₀     : ObjC → ObjD
    F₁     : {A B : ObjC} → HomC A B → HomD (F₀ A) (F₀ B)

    F-id   : {A : ObjC} → F₁ (Category.id C A) ≡ Category.id D (F₀ A)
    F-comp : {A B C′ : ObjC}
             → (f : HomC A B) (g : HomC B C′)
             → F₁ (Category._∘_ C f g) ≡ Category._∘_ D (F₁ f) (F₁ g)

------------------------------------------------------------------------
-- Path ⇒ ≤
------------------------------------------------------------------------

-- Each edge increases time strictly, hence a ≤-morphism exists.
edge⇒≤ : ∀ {G u v} → (e : u DG.—→ v within G) → u ≤ v
edge⇒≤ {G} {u} {v} e = Cut.<⇒≤ (DG.edge-increases-time u v G e)

-- Recursively map a Path to a single ≤-witness
path⇒≤ : ∀ {G u v} → PC.Path G u v → u ≤ v
path⇒≤ {G} {u} {v} PC.refl-path     = ≤-refl
path⇒≤ {G} {u} {w} (e PC.∷-path p)  = ≤-trans (edge⇒≤ {G} e) (path⇒≤ {G} p)

-- Compatibility with concatenation
path⇒≤-++ :
  ∀ {G a b c} (p : PC.Path G a b) (q : PC.Path G b c) →
  path⇒≤ (p PC.++-path q) ≡ ≤-trans (path⇒≤ p) (path⇒≤ q)
path⇒≤-++ {G} PC.refl-path q = Cut.≤-idˡ (path⇒≤ {G} q)
path⇒≤-++ {G} (e PC.∷-path p) q
  rewrite path⇒≤-++ {G} p q
        | Cut.≤-assoc (edge⇒≤ {G} e) (path⇒≤ {G} p) (path⇒≤ {G} q)
  = refl

------------------------------------------------------------------------
-- The functor R(G) → CutCat
------------------------------------------------------------------------

PathToCut : (G : DG.DriftGraph) →
  Functor (DG.NodeId) (PC.Path G) (PC.DriftPathCategory G)
          (ℕ)        (_≤_)       (Cut.CutCat)
PathToCut G = record
  { F₀     = λ x → x
  ; F₁     = λ {A} {B} p → path⇒≤ {G} {A} {B} p
  ; F-id   = λ {A} → refl
  ; F-comp = λ f g → path⇒≤-++ {G} f g
  }