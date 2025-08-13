{-# OPTIONS --safe #-}

module Structures.Step8_PathCategory where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_)

-- Import the verified drift graph structure from Step 7
open import Structures.Step7_DriftGraph as DG

------------------------------------------------------------------------
-- 1. CATEGORICAL PATH STRUCTURE
------------------------------------------------------------------------

-- | Definition: A path in a drift graph is either the identity path
-- | or an edge followed by another path. This forms the morphisms
-- | of our reachability category.
data Path (G : DG.DriftGraph) : DG.NodeId → DG.NodeId → Set where
  refl-path : ∀ {u} → Path G u u
  _∷-path_  : ∀ {u v w} → (e : u DG.—→ v within G) → Path G v w → Path G u w

infixr 5 _∷-path_

------------------------------------------------------------------------
-- 2. PATH COMPOSITION OPERATION
------------------------------------------------------------------------

-- | Path composition via structural recursion. This operation
-- | concatenates two paths while preserving type-level connectivity.
_++-path_ : ∀ {G u v w} → Path G u v → Path G v w → Path G u w
refl-path      ++-path q = q
(e ∷-path p) ++-path q = e ∷-path (p ++-path q)

infixr 5 _++-path_

------------------------------------------------------------------------
-- 3. CATEGORICAL LAWS: RIGOROUS PROOFS BY STRUCTURAL INDUCTION
------------------------------------------------------------------------

-- | Theorem: Path composition is associative
-- | Proof: By structural induction on the first path argument
path-assoc : ∀ {G a b c d} (p : Path G a b) (q : Path G b c) (r : Path G c d) →
             (p ++-path q) ++-path r ≡ p ++-path (q ++-path r)
path-assoc refl-path      q r = refl
path-assoc (e ∷-path p) q r = cong (e ∷-path_) (path-assoc p q r)

-- | Theorem: Identity path is left-neutral for composition
-- | Proof: Immediate by definition of path composition
path-idˡ : ∀ {G u v} (p : Path G u v) → refl-path ++-path p ≡ p
path-idˡ p = refl

-- | Theorem: Identity path is right-neutral for composition  
-- | Proof: By structural induction on path structure
path-idʳ : ∀ {G u v} (p : Path G u v) → p ++-path refl-path ≡ p
path-idʳ refl-path      = refl
path-idʳ (e ∷-path p) = cong (e ∷-path_) (path-idʳ p)

------------------------------------------------------------------------
-- 4. ABSTRACT CATEGORY INTERFACE
------------------------------------------------------------------------

-- | Definition: Abstract categorical structure with objects and morphisms
-- | satisfying the standard category laws
record Category (Obj : Set) (Hom : Obj → Obj → Set) : Set₁ where
  field
    id    : ∀ A → Hom A A
    _∘_   : ∀ {A B C} → Hom A B → Hom B C → Hom A C

    -- Category laws
    idˡ   : ∀ {A B} (f : Hom A B) → (id A) ∘ f ≡ f
    idʳ   : ∀ {A B} (f : Hom A B) → f ∘ (id B) ≡ f  
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

------------------------------------------------------------------------
-- 5. REACHABILITY CATEGORY CONSTRUCTION
------------------------------------------------------------------------

-- | Construction: The reachability category R(G) for a drift graph G
-- | Objects: Node identifiers from the drift graph
-- | Morphisms: Paths as defined above
-- | Laws: Proven using the structural properties of paths
DriftPathCategory : (G : DG.DriftGraph) → Category (DG.NodeId) (Path G)
DriftPathCategory G = record
  { id    = λ A → refl-path        -- Identity morphism constructor
  ; _∘_   = _++-path_              -- Path composition as morphism composition  
  ; idˡ   = λ f → path-idˡ f       -- Left identity law
  ; idʳ   = λ f → path-idʳ f       -- Right identity law
  ; assoc = λ f g h → path-assoc f g h  -- Associativity law
  }

------------------------------------------------------------------------
-- 6. VERIFICATION AND TESTING INTERFACE
------------------------------------------------------------------------

-- | Test: Single-edge path construction
test-single-path : ∀ {G u v} → (e : u DG.—→ v within G) → Path G u v
test-single-path e = e ∷-path refl-path

-- | Test: Identity morphism access via category interface
test-identity : ∀ {G u} → Path G u u  
test-identity {G} {u} = Category.id (DriftPathCategory G) u

-- | Test: Morphism composition via category interface  
test-composition : ∀ {G u v w} → Path G u v → Path G v w → Path G u w
test-composition {G} p q = Category._∘_ (DriftPathCategory G) p q

-- | Verification: Left identity law holds
test-left-id : ∀ {G u v} (p : Path G u v) → 
               Category._∘_ (DriftPathCategory G) (Category.id (DriftPathCategory G) u) p ≡ p
test-left-id {G} p = Category.idˡ (DriftPathCategory G) p

-- | Verification: Right identity law holds
test-right-id : ∀ {G u v} (p : Path G u v) → 
                Category._∘_ (DriftPathCategory G) p (Category.id (DriftPathCategory G) v) ≡ p  
test-right-id {G} p = Category.idʳ (DriftPathCategory G) p

