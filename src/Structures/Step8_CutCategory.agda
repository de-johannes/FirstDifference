{-# OPTIONS --safe #-}

module Structures.Step8_CutCategory where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

-- | Import the general Category structure from our rigorous Step 8
open import Structures.Step8_PathCategory using (Category)

------------------------------------------------------------------------
-- 1. CATEGORICAL LAWS FOR TEMPORAL ORDERING
------------------------------------------------------------------------

-- | Private proofs: All proofs for `m ≤ n` are propositionally equal
-- | This captures the "thinness" property of temporal categories
private
  ≤-idˡ : ∀ {m n : ℕ} (p : m ≤ n) → ≤-trans ≤-refl p ≡ p
  ≤-idˡ p = ≤-irrelevant (≤-trans ≤-refl p) p

  ≤-idʳ : ∀ {m n : ℕ} (p : m ≤ n) → ≤-trans p ≤-refl ≡ p
  ≤-idʳ p = ≤-irrelevant (≤-trans p ≤-refl) p

  ≤-assoc : ∀ {m n k l : ℕ} (p : m ≤ n) (q : n ≤ k) (r : k ≤ l) →
            ≤-trans (≤-trans p q) r ≡ ≤-trans p (≤-trans q r)
  ≤-assoc p q r = ≤-irrelevant (≤-trans (≤-trans p q) r) (≤-trans p (≤-trans q r))

-- | Helper: Convert strict inequality to non-strict inequality
-- | Since m < n is defined as suc m ≤ n, we prove m ≤ n by induction
<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ {zero} {suc n} _ = z≤n
<⇒≤ {suc m} {suc n} (s≤s m<n) = s≤s (<⇒≤ m<n)

------------------------------------------------------------------------
-- 2. CUTCAT: THE CANONICAL TEMPORAL CATEGORY
------------------------------------------------------------------------

-- | Construction: CutCat as instance of the general Category structure
-- | Objects: Natural numbers representing temporal stages
-- | Morphisms: ≤-relation representing temporal ordering
-- | This demonstrates modular categorical construction
CutCat : Category ℕ _≤_
CutCat = record
  { id    = λ A → ≤-refl              -- Identity: reflexivity function
  ; _∘_   = λ f g → ≤-trans f g       -- Composition: f : A→B, g : B→C gives A→C
  ; idˡ   = ≤-idˡ                     -- Left identity law
  ; idʳ   = ≤-idʳ                     -- Right identity law  
  ; assoc = λ f g h → ≤-assoc f g h   -- Associativity law
  }

------------------------------------------------------------------------
-- 3. TEMPORAL PROPERTIES AND THEOREMS
------------------------------------------------------------------------

-- | Theorem: Strict temporal ordering implies morphism existence
-- | For m < n, there exists a unique morphism m → n in CutCat
-- | Using Σ-type (dependent pair) for existential quantification
temporal-strict : ∀ {m n : ℕ} → m < n → Σ (m ≤ n) (λ _ → ⊤)
temporal-strict {m} {n} m<n = (<⇒≤ m<n , tt)

-- | Theorem: Temporal ordering is antisymmetric
-- | Bidirectional morphisms imply object equality
temporal-antisym : ∀ {m n : ℕ} → (m ≤ n) → (n ≤ m) → m ≡ n
temporal-antisym = ≤-antisym

------------------------------------------------------------------------
-- 4. VERIFICATION AND TESTING INTERFACE
------------------------------------------------------------------------

-- | Test: Temporal progression morphism construction (2 ≤ 5)
-- | Proof: 2 = suc(suc(0)), 5 = suc^5(0), so we need 0 ≤ 3 + 2 s≤s applications
temporal-test-progression : 2 ≤ 5
temporal-test-progression = s≤s (s≤s z≤n)    -- z≤n : 0 ≤ 3, then 1 ≤ 4, then 2 ≤ 5

-- | Test: Identity morphism via category interface
temporal-test-identity : 5 ≤ 5
temporal-test-identity = Category.id CutCat 5

-- | Test: Another temporal progression (5 ≤ 7)
-- | Proof: 5 = suc^5(0), 7 = suc^7(0), so we need 0 ≤ 2 + 5 s≤s applications  
temporal-test-progression-2 : 5 ≤ 7
temporal-test-progression-2 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))  -- 0≤2, 1≤3, 2≤4, 3≤5, 4≤6, 5≤7

-- | Test: Temporal morphism composition via category interface (2 ≤ 7)
temporal-test-composition : 2 ≤ 7
temporal-test-composition = Category._∘_ CutCat temporal-test-progression temporal-test-progression-2

-- | Verification: Category laws preserved for temporal morphisms
temporal-test-left-identity : ∀ {m n : ℕ} (f : m ≤ n) →
                              Category._∘_ CutCat (Category.id CutCat m) f ≡ f
temporal-test-left-identity f = Category.idˡ CutCat f

temporal-test-right-identity : ∀ {m n : ℕ} (f : m ≤ n) →
                               Category._∘_ CutCat f (Category.id CutCat n) ≡ f  
temporal-test-right-identity f = Category.idʳ CutCat f

temporal-test-associativity : ∀ {m n k l : ℕ} (f : m ≤ n) (g : n ≤ k) (h : k ≤ l) →
                              Category._∘_ CutCat (Category._∘_ CutCat f g) h 
                              ≡ Category._∘_ CutCat f (Category._∘_ CutCat g h)
temporal-test-associativity f g h = Category.assoc CutCat f g h

------------------------------------------------------------------------
-- RESULT: Modular temporal category construction with rigorous verification
-- Demonstrates proper categorical abstraction and module reuse
-- Ready for functor construction between reachability and temporal categories
------------------------------------------------------------------------
