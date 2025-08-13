{-# OPTIONS --safe #-}

module Structures.Step8_TemporalFunctor where

open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)
open import Function using (id)

-- Import our actual modules (not _Final versions)
open import Structures.Step7_DriftGraph as DG using (DriftGraph; NodeId; _—→_within_; 
                                                     edge-increases-time)
open import Structures.Step8_PathCategory as PC using (Category; DriftPathCategory; 
                                                       Path; refl-path; _∷-path_; _++-path_)
open import Structures.Step8_CutCategory as TC using (CutCat; <⇒≤)

------------------------------------------------------------------------
-- 1. FUNCTOR INTERFACE (as before)
------------------------------------------------------------------------

record Functor (C D : Category _ _) : Set₁ where
  private
    module C = Category C
    module D = Category D
  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {X Y} → C.Hom X Y → D.Hom (F₀ X) (F₀ Y)
    
    preserves-id : ∀ {X} → F₁ (C.id X) ≡ D.id (F₀ X)
    preserves-comp : ∀ {X Y Z} (f : C.Hom X Y) (g : C.Hom Y Z) 
                   → F₁ (C._∘_ f g) ≡ D._∘_ (F₁ f) (F₁ g)

------------------------------------------------------------------------
-- 2. CLEAN OBJECT AND MORPHISM MAPPINGS
------------------------------------------------------------------------

-- Object mapping: NodeId → ℕ (identity since both are ℕ)
π-obj : NodeId → ℕ
π-obj = id

-- Morphism mapping: Path to temporal ordering proof
π-hom : ∀ {G : DriftGraph} {u v : NodeId} → Path G u v → π-obj u ≤ π-obj v
π-hom refl-path = ≤-refl
π-hom (e ∷-path p) = ≤-trans (<⇒≤ (edge-increases-time _ _ _ e)) (π-hom p)

------------------------------------------------------------------------
-- 3. FUNCTOR LAW PROOFS: LEVERAGING THINNESS
------------------------------------------------------------------------

-- Identity preservation: Direct by definition
π-preserves-id : ∀ {G : DriftGraph} {u : NodeId} → 
                 π-hom (refl-path {G} {u}) ≡ ≤-refl
π-preserves-id = refl

-- Composition preservation: The key insight - use ≤-irrelevant!
-- Since CutCat is thin, all parallel arrows are equal
π-preserves-comp : ∀ {G : DriftGraph} {u v w : NodeId} 
                   (p : Path G u v) (q : Path G v w) →
                   π-hom (p PC.++-path q) ≡ 
                   Category._∘_ TC.CutCat (π-hom p) (π-hom q)
π-preserves-comp p q = ≤-irrelevant _ _
  -- Both sides have type (π-obj u ≤ π-obj w), and CutCat is thin!

------------------------------------------------------------------------
-- 4. THE TEMPORAL PROJECTION FUNCTOR
------------------------------------------------------------------------

-- The bridge between causal structure and temporal ordering
TemporalProjection : (G : DriftGraph) → Functor (DriftPathCategory G) TC.CutCat
TemporalProjection G = record
  { F₀ = π-obj
  ; F₁ = π-hom  
  ; preserves-id = π-preserves-id
  ; preserves-comp = π-preserves-comp
  }

------------------------------------------------------------------------
-- 5. MATHEMATICAL SIGNIFICANCE AND TESTS
------------------------------------------------------------------------

-- Test: Identity preservation
temporal-test-identity : ∀ {G : DriftGraph} {u : NodeId} →
                         Functor.F₁ (TemporalProjection G) (refl-path {G} {u}) ≡ ≤-refl
temporal-test-identity = refl

-- Test: Single edge mapping
temporal-test-edge : ∀ {G : DriftGraph} {u v : NodeId} (e : u DG.—→ v within G) →
                     Functor.F₁ (TemporalProjection G) (e ∷-path refl-path) ≡
                     <⇒≤ (edge-increases-time u v G e)
temporal-test-edge e = refl

-- The profound insight: Causal paths project to temporal ordering
causal-to-temporal : ∀ {G : DriftGraph} {u v : NodeId} →
                     Path G u v → (u ≤ v)
causal-to-temporal {G} path = Functor.F₁ (TemporalProjection G) path

------------------------------------------------------------------------
-- RESULT: The mathematical bridge between causality and temporality
-- Rigorous functor with trivial proofs thanks to thin category structure
-- Foundation for understanding how complex causal webs project onto linear time
------------------------------------------------------------------------
