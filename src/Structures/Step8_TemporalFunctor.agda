{-# OPTIONS --safe #-}

module Structures.Step8_TemporalFunctor where

open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)
open import Function using (id)

-- Import our actual modules
open import Structures.Step7_DriftGraph as DG using (DriftGraph; NodeId; _—→_within_; 
                                                     edge-increases-time)
open import Structures.Step8_PathCategory as PC using (Category; DriftPathCategory; 
                                                       Path; refl-path; _∷-path_; _++-path_)
open import Structures.Step8_CutCategory as TC using (CutCat; <⇒≤)

------------------------------------------------------------------------
-- 1. FUNCTOR INTERFACE: ADAPTED TO OUR CATEGORY STRUCTURE
------------------------------------------------------------------------

-- | Functor between categories with explicit object and morphism types
-- | Our Category record: Category (Obj : Set) (Hom : Obj → Obj → Set)
record Functor {ObjC ObjD : Set} {HomC : ObjC → ObjC → Set} {HomD : ObjD → ObjD → Set}
               (C : Category ObjC HomC) (D : Category ObjD HomD) : Set₁ where
  field
    -- Object and morphism mappings
    F₀ : ObjC → ObjD
    F₁ : ∀ {X Y} → HomC X Y → HomD (F₀ X) (F₀ Y)
    
    -- Functor laws: structure preservation
    preserves-id : ∀ {X} → F₁ (Category.id C X) ≡ Category.id D (F₀ X)
    preserves-comp : ∀ {X Y Z} (f : HomC X Y) (g : HomC Y Z) 
                   → F₁ (Category._∘_ C f g) ≡ Category._∘_ D (F₁ f) (F₁ g)

------------------------------------------------------------------------
-- 2. OBJECT AND MORPHISM MAPPINGS
------------------------------------------------------------------------

-- | Object mapping: NodeId → ℕ (identity since both are ℕ)
π-obj : NodeId → ℕ
π-obj = id

-- | Morphism mapping: Path to temporal ordering proof
π-hom : ∀ (G : DriftGraph) {u v : NodeId} → Path G u v → π-obj u ≤ π-obj v
π-hom G refl-path = ≤-refl
π-hom G (e ∷-path p) = ≤-trans (<⇒≤ (edge-increases-time _ _ G e)) (π-hom G p)

------------------------------------------------------------------------
-- 3. HELPER LEMMAS FOR TEMPORAL ORDERING
------------------------------------------------------------------------

-- | Right identity for ≤-trans (we need this for proofs)
private
  ≤-idʳ : ∀ {m n : ℕ} (p : m ≤ n) → ≤-trans p ≤-refl ≡ p
  ≤-idʳ p = ≤-irrelevant (≤-trans p ≤-refl) p

------------------------------------------------------------------------
-- 4. FUNCTOR LAW PROOFS: LEVERAGING THINNESS
------------------------------------------------------------------------

-- | Identity preservation: Direct by definition
π-preserves-id : ∀ (G : DriftGraph) {u : NodeId} → 
                 π-hom G (Category.id (DriftPathCategory G) u) ≡ 
                 Category.id TC.CutCat (π-obj u)
π-preserves-id G = refl

-- | Composition preservation: Key insight - use ≤-irrelevant!
-- | Since CutCat is thin, all parallel arrows are equal
π-preserves-comp : ∀ (G : DriftGraph) {u v w : NodeId} 
                   (p : Path G u v) (q : Path G v w) →
                   π-hom G (Category._∘_ (DriftPathCategory G) p q) ≡ 
                   Category._∘_ TC.CutCat (π-hom G p) (π-hom G q)
π-preserves-comp G p q = ≤-irrelevant _ _
  -- Both sides have type (π-obj u ≤ π-obj w), and CutCat is thin!

------------------------------------------------------------------------
-- 5. THE TEMPORAL PROJECTION FUNCTOR
------------------------------------------------------------------------

-- | The bridge between causal structure and temporal ordering
TemporalProjection : (G : DriftGraph) → 
                     Functor (DriftPathCategory G) TC.CutCat
TemporalProjection G = record
  { F₀ = π-obj
  ; F₁ = π-hom G  
  ; preserves-id = π-preserves-id G
  ; preserves-comp = π-preserves-comp G
  }

------------------------------------------------------------------------
-- 6. MATHEMATICAL SIGNIFICANCE AND TESTS
------------------------------------------------------------------------

-- | Test: Identity preservation
temporal-test-identity : ∀ (G : DriftGraph) {u : NodeId} →
                         Functor.F₁ (TemporalProjection G) (refl-path {G} {u}) ≡ ≤-refl
temporal-test-identity G = refl

-- | Test: Single edge mapping (now with explicit parameters)
temporal-test-edge : ∀ (G : DriftGraph) {u v : NodeId} (e : u DG.—→ v within G) →
                     Functor.F₁ (TemporalProjection G) (e ∷-path refl-path) ≡
                     <⇒≤ (edge-increases-time u v G e)
temporal-test-edge G e = ≤-idʳ (<⇒≤ (edge-increases-time _ _ G e))

-- | The profound insight: Causal paths project to temporal ordering
causal-to-temporal : ∀ (G : DriftGraph) {u v : NodeId} →
                     Path G u v → (u ≤ v)
causal-to-temporal G path = Functor.F₁ (TemporalProjection G) path

-- | Test: Composition preservation verification
temporal-test-composition : ∀ (G : DriftGraph) {u v w : NodeId}
                            (p : Path G u v) (q : Path G v w) →
                            Functor.F₁ (TemporalProjection G) (p PC.++-path q) ≡
                            Category._∘_ TC.CutCat 
                              (Functor.F₁ (TemporalProjection G) p)
                              (Functor.F₁ (TemporalProjection G) q)
temporal-test-composition G p q = Functor.preserves-comp (TemporalProjection G) p q

-- | Test: Path length and temporal distance correlation
temporal-distance-preservation : ∀ (G : DriftGraph) {u v : NodeId}
                                  (path : Path G u v) →
                                  u ≤ v
temporal-distance-preservation G path = causal-to-temporal G path

------------------------------------------------------------------------
-- RESULT: The mathematical bridge between causality and temporality
-- Complete functor with rigorous proofs using thin category properties
-- Demonstrates how causal graph structure projects onto temporal ordering
------------------------------------------------------------------------
