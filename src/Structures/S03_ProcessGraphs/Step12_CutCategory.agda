{-# OPTIONS --safe #-}

-- | Step 12: Cut Category (temporal category on ℕ with ≤)
-- | Objects are natural numbers (time indices), morphisms are ≤ proofs.
module Structures.S03_ProcessGraphs.Step12_CutCategory where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

-- Pull the generic Category record
open import Structures.S03_ProcessGraphs.Step11_PathCategory using (Category)

------------------------------------------------------------------------
-- Elementary equalities for ≤ (exported, not private)
------------------------------------------------------------------------

≤-idˡ : ∀ {m n : ℕ} (p : m ≤ n) → ≤-trans ≤-refl p ≡ p
≤-idˡ p = ≤-irrelevant (≤-trans ≤-refl p) p

≤-idʳ : ∀ {m n : ℕ} (p : m ≤ n) → ≤-trans p ≤-refl ≡ p
≤-idʳ p = ≤-irrelevant (≤-trans p ≤-refl) p

≤-assoc : ∀ {m n k l : ℕ} (p : m ≤ n) (q : n ≤ k) (r : k ≤ l) →
          ≤-trans (≤-trans p q) r ≡ ≤-trans p (≤-trans q r)
≤-assoc p q r =
  ≤-irrelevant (≤-trans (≤-trans p q) r) (≤-trans p (≤-trans q r))

-- Strict-to-nonstrict conversion (m < n  ⇒  m ≤ n)
<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ {zero}  {suc n} _           = z≤n
<⇒≤ {suc m} {suc n} (s≤s m<n)   = s≤s (<⇒≤ m<n)

------------------------------------------------------------------------
-- The temporal category on ℕ
------------------------------------------------------------------------

CutCat : Category ℕ _≤_
CutCat = record
  { id    = λ A → ≤-refl
  ; _∘_   = λ {A B C} f g → ≤-trans f g
  ; idˡ   = ≤-idˡ
  ; idʳ   = ≤-idʳ
  ; assoc = λ {A B C D} f g h → ≤-assoc f g h
  }

------------------------------------------------------------------------
-- Small theorems / interface
------------------------------------------------------------------------

-- Existence: m < n gives a morphism m → n in CutCat
temporal-strict : ∀ {m n : ℕ} → m < n → Σ (m ≤ n) (λ _ → ⊤)
temporal-strict m<n = (<⇒≤ m<n , tt)

-- Antisymmetry: parallel morphisms both ways force equality
temporal-antisym : ∀ {m n : ℕ} → (m ≤ n) → (n ≤ m) → m ≡ n
temporal-antisym = ≤-antisym