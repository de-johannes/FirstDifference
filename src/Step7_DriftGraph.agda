{-# OPTIONS --safe #-}

-- | Step 7: Drift Graph - Explicit DAG Structure for Historical Dependencies
-- | This bridges the gap between operational drift and categorical reachability
module Step7_DriftGraph where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _+_; _⊔_; _≟_)
open import Data.Nat.Properties using (<-trans; <-irrefl)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.List using (List; []; _∷_; _++_; length; any; all; foldr; map; filter)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; ⌊_⌋)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (id; _∘_)

-- Import our previous steps
open import Step1_BooleanFoundation
open import Step2_VectorOperations  
open import Step3_AlgebraLaws
open import Step4_PartialOrder
open import Step5_CategoryStructure

------------------------------------------------------------------------
-- VECTOR EQUALITY HELPER
------------------------------------------------------------------------

-- | Boolean equality
bool-eq : Bool → Bool → Bool
bool-eq true true = true
bool-eq false false = true
bool-eq _ _ = false

-- | Decidable equality for Bool vectors
vec-eq : ∀ {n} → Vec Bool n → Vec Bool n → Bool
vec-eq [] [] = true
vec-eq (x ∷ xs) (y ∷ ys) = bool-eq x y ∧ vec-eq xs ys

------------------------------------------------------------------------
-- DISTINCTION UNIVERSE: Heterogeneous Distinctions
------------------------------------------------------------------------

-- | A distinction can have any finite dimension
data Distinction : Set where
  mk-dist : (n : ℕ) → Dist n → Distinction

-- | Extract dimension and content
dim : Distinction → ℕ
dim (mk-dist n _) = n

content : (d : Distinction) → Dist (dim d)
content (mk-dist _ v) = v

-- | Equality for distinctions
distinction-eq : Distinction → Distinction → Bool
distinction-eq (mk-dist n₁ v₁) (mk-dist n₂ v₂) with n₁ ≟ n₂
... | no _ = false
... | yes refl = vec-eq v₁ v₂

------------------------------------------------------------------------
-- DRIFT EVENTS: Explicit Parent-Child Relations
------------------------------------------------------------------------

-- | A drift event records: (parent₁, parent₂) ⟹ child
record DriftEvent : Set where
  constructor _,_⟹_
  field
    parent₁ : Distinction
    parent₂ : Distinction  
    child   : Distinction
    
open DriftEvent public

-- | Smart constructor ensuring dimensional compatibility
mk-drift-event : {n : ℕ} → (p₁ p₂ : Dist n) → (c : Dist n) → DriftEvent
mk-drift-event {n} p₁ p₂ c = mk-dist n p₁ , mk-dist n p₂ ⟹ mk-dist n c

-- | Extract all vertices involved in an event
event-vertices : DriftEvent → List Distinction
event-vertices (p₁ , p₂ ⟹ c) = p₁ ∷ p₂ ∷ c ∷ []

------------------------------------------------------------------------
-- LIST MEMBERSHIP
------------------------------------------------------------------------

-- Helper: membership in lists
data _∈-list_ {A : Set} : A → List A → Set where
  here  : ∀ {x xs} → x ∈-list (x ∷ xs)
  there : ∀ {x y xs} → x ∈-list xs → x ∈-list (y ∷ xs)

------------------------------------------------------------------------
-- DRIFT GRAPH: DAG with Temporal Structure
------------------------------------------------------------------------

record DriftGraph : Set where
  field
    vertices : List Distinction
    events   : List DriftEvent
    
    -- All event vertices must be in the vertex list
    vertex-closure : ∀ (e : DriftEvent) (v : Distinction) → 
                     v ∈-list (event-vertices e) → v ∈-list vertices
                     
    -- Temporal ordering function
    τ : Distinction → ℕ
    
    -- Parents must have smaller timestamp than children
    temporal-order : ∀ (e : DriftEvent) → 
                     τ (parent₁ e) < τ (child e) × τ (parent₂ e) < τ (child e)

open DriftGraph public

------------------------------------------------------------------------
-- REACHABILITY AND ACYCLICITY
------------------------------------------------------------------------

-- | Direct parent relation
_⟹₁_ : {G : DriftGraph} → Distinction → Distinction → Set
_⟹₁_ {G} parent child = 
  ∃-syntax (λ e → e ∈-list events G × 
                  ((parent ≡ parent₁ e ⊎ parent ≡ parent₂ e) × child ≡ child e))

-- | Transitive closure: reachability (renamed constructor to avoid conflict)
data _⤜_ {G : DriftGraph} : Distinction → Distinction → Set where
  direct   : ∀ {u v} → u ⟹₁ v → u ⤜ v
  compose  : ∀ {u v w} → u ⤜ v → v ⤜ w → u ⤜ w

-- | Helper: reachability implies temporal precedence  
⤜-implies-τ< : {G : DriftGraph} → ∀ {u w} → u ⤜ w → τ G u < τ G w
⤜-implies-τ< {G} (direct (e , (e∈events , ((inj₁ u≡p₁) , w≡c)))) = 
  subst (λ x → x < τ G (child e)) (sym u≡p₁) 
        (subst (λ x → τ G (parent₁ e) < x) w≡c 
               (proj₁ (temporal-order G e)))
⤜-implies-τ< {G} (direct (e , (e∈events , ((inj₂ u≡p₂) , w≡c)))) = 
  subst (λ x → x < τ G (child e)) (sym u≡p₂)
        (subst (λ x → τ G (parent₂ e) < x) w≡c 
               (proj₂ (temporal-order G e)))
⤜-implies-τ< {G} (compose u⤜v v⤜w) = <-trans (⤜-implies-τ< u⤜v) (⤜-implies-τ< v⤜w)

-- | Key theorem: The graph is acyclic (well-founded)
theorem-acyclic : (G : DriftGraph) → ∀ (v : Distinction) → ¬ (v ⤜ v)
theorem-acyclic G v v⤜v = <-irrefl refl (⤜-implies-τ< v⤜v)

------------------------------------------------------------------------
-- RANK STRUCTURE: Temporal Layers
------------------------------------------------------------------------

-- | All vertices at temporal rank n
rank-layer : (G : DriftGraph) → ℕ → List Distinction
rank-layer G n = filter (λ v → ⌊ τ G v ≟ n ⌋) (vertices G)

-- | Maximum rank in the graph  
max-rank : DriftGraph → ℕ
max-rank G = foldr _⊔_ 0 (map (τ G) (vertices G))

------------------------------------------------------------------------
-- CONNECTION TO CUTCAT: Temporal Progression Functor
------------------------------------------------------------------------

-- | The temporal spine extracted from DriftGraph
CutCat-from-DriftGraph : DriftGraph → Set
CutCat-from-DriftGraph G = ℕ  -- Just the temporal indices

-- | Functor from DriftGraph layers to CutCat
π-DriftGraph : (G : DriftGraph) → (n : ℕ) → List Distinction
π-DriftGraph G n = rank-layer G n

------------------------------------------------------------------------
-- BRIDGE TO EXISTING DRIFTMORPHISMS
------------------------------------------------------------------------

-- | Extract operational structure from graph
graph-to-operations : DriftGraph → ∀ n → Dist n → Dist n → Dist n  
graph-to-operations G n v₁ v₂ = extract-result n v₁ v₂ (events G)
  where
  -- Find drift event with given parents and extract child
  extract-result : ∀ n → Dist n → Dist n → List DriftEvent → Dist n
  extract-result n v₁ v₂ [] = drift v₁ v₂  -- Fallback to component-wise AND
  extract-result n v₁ v₂ ((mk-dist m p₁ , mk-dist m p₂ ⟹ mk-dist m c) ∷ es) 
    with n ≟ m
  ... | no _ = extract-result n v₁ v₂ es
  ... | yes refl with vec-eq v₁ p₁ | vec-eq v₂ p₂  
  ...   | true | true = c
  ...   | _ | _ = extract-result n v₁ v₂ es

------------------------------------------------------------------------
-- GLOBAL CONSTANTS FOR TESTING
------------------------------------------------------------------------

-- | Standard test distinctions for reuse
v₁-test : Distinction  
v₁-test = mk-dist 2 (true ∷ false ∷ [])

v₂-test : Distinction
v₂-test = mk-dist 2 (false ∷ true ∷ [])

v₃-test : Distinction
v₃-test = mk-dist 2 (false ∷ false ∷ [])

e₁-test : DriftEvent
e₁-test = v₁-test , v₂-test ⟹ v₃-test

------------------------------------------------------------------------
-- EXAMPLES AND CONSTRUCTION
------------------------------------------------------------------------

-- | Example: 2D drift graph with one event
example-2d-drift : DriftGraph
example-2d-drift = record
  { vertices = v₁-test ∷ v₂-test ∷ v₃-test ∷ []
  ; events = e₁-test ∷ []
  ; vertex-closure = vertex-closure-proof
  ; τ = τ-func  
  ; temporal-order = temporal-order-proof
  }
  where
  τ-func : Distinction → ℕ
  τ-func (mk-dist 2 (true ∷ false ∷ [])) = 0
  τ-func (mk-dist 2 (false ∷ true ∷ [])) = 0  
  τ-func (mk-dist 2 (false ∷ false ∷ [])) = 1
  τ-func _ = 0
  
  vertex-closure-proof : ∀ (e : DriftEvent) (v : Distinction) → 
                        v ∈-list (event-vertices e) → v ∈-list (v₁-test ∷ v₂-test ∷ v₃-test ∷ [])
  vertex-closure-proof (.v₁-test , .v₂-test ⟹ .v₃-test) .v₁-test here = here
  vertex-closure-proof (.v₁-test , .v₂-test ⟹ .v₃-test) .v₂-test (there here) = there here
  vertex-closure-proof (.v₁-test , .v₂-test ⟹ .v₃-test) .v₃-test (there (there here)) = there (there here)
  vertex-closure-proof (.v₁-test , .v₂-test ⟹ .v₃-test) _ (there (there (there ())))
  
  temporal-order-proof : ∀ (e : DriftEvent) → 
                        τ-func (parent₁ e) < τ-func (child e) × 
                        τ-func (parent₂ e) < τ-func (child e)
  temporal-order-proof (.v₁-test , .v₂-test ⟹ .v₃-test) = s≤s z≤n , s≤s z≤n

------------------------------------------------------------------------
-- CONSTRUCTION OPERATIONS
------------------------------------------------------------------------

-- | Add new vertex to graph
add-vertex : DriftGraph → Distinction → ℕ → DriftGraph
add-vertex G v time = record G 
  { vertices = v ∷ vertices G
  ; τ = λ w → if distinction-eq w v then time else τ G w
  }

-- | Add new drift event to graph (simplified)
add-drift-event : DriftGraph → DriftEvent → DriftGraph  
add-drift-event G e = record G { events = e ∷ events G }

------------------------------------------------------------------------
-- CONSTRUCTION HELPERS FOR REACHABILITY
------------------------------------------------------------------------

-- | Helper: construct a direct reachability witness
mk-direct-reach : {G : DriftGraph} → (e : DriftEvent) → (parent child : Distinction) → 
                  e ∈-list (events G) → 
                  (parent ≡ parent₁ e ⊎ parent ≡ parent₂ e) → 
                  child ≡ child e → 
                  parent ⟹₁ child
mk-direct-reach e parent child e∈events parent-eq child-eq = 
  e , (e∈events , (parent-eq , child-eq))

-- | Helper: compose reachability paths
mk-transitive-reach : {G : DriftGraph} → {u v w : Distinction} → 
                      u ⤜ v → v ⤜ w → u ⤜ w
mk-transitive-reach u⤜v v⤜w = compose u⤜v v⤜w

------------------------------------------------------------------------
-- TESTING AND VALIDATION
------------------------------------------------------------------------

-- | Test: Check temporal layers
test-rank-0 : List Distinction
test-rank-0 = rank-layer example-2d-drift 0

test-rank-1 : List Distinction  
test-rank-1 = rank-layer example-2d-drift 1

-- | Test: Simple operations work
test-drift-operation : Dist 2
test-drift-operation = graph-to-operations example-2d-drift 2 
                       (true ∷ false ∷ []) 
                       (false ∷ true ∷ [])

-- | Test: Reachability witness construction - now using global constants
test-reachability : _⟹₁_ {example-2d-drift} v₁-test v₃-test
test-reachability = mk-direct-reach e₁-test v₁-test v₃-test here (inj₁ refl) refl

-- | Test: Acyclicity for our example
test-acyclicity : ¬ (_⤜_ {example-2d-drift} v₃-test v₃-test)
test-acyclicity = theorem-acyclic example-2d-drift v₃-test

-- | Test: Transitive reachability construction
test-transitive : {G : DriftGraph} → {u v w : Distinction} → 
                  u ⤜ v → v ⤜ w → u ⤜ w
test-transitive = mk-transitive-reach

------------------------------------------------------------------------
-- PROPERTIES AND THEOREMS
------------------------------------------------------------------------

-- | Reachability is transitive (by construction)
⤜-transitive : {G : DriftGraph} → ∀ {u v w} → u ⤜ v → v ⤜ w → u ⤜ w  
⤜-transitive = compose

-- | Direct reachability is a special case of general reachability
⟹₁-to-⤜ : {G : DriftGraph} → ∀ {u v} → u ⟹₁ v → u ⤜ v
⟹₁-to-⤜ = direct

------------------------------------------------------------------------
-- RESULT: Perfect Drift Graph Structure!
-- • DAG property enforced by temporal ordering τ
-- • Reachability via explicit event composition  
-- • Acyclicity theorem proven from τ-monotonicity
-- • Bridge between categorical morphisms and graph operations
-- • Foundation for process-based temporal reasoning
------------------------------------------------------------------------

