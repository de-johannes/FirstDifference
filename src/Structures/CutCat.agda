module Structures.CutCat where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total)

------------------------------------------------------------------------
-- Temporal ordering: foundation for irreversible progression
-- Uses standard Data.Nat.≤ relation - clean and simple!
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Category interface: minimal structure for our purposes
------------------------------------------------------------------------

record Category (ℓ : Level) : Set (lsuc ℓ) where
  field
    Obj   : Set ℓ
    Hom   : Obj → Obj → Set ℓ
    id    : ∀ A → Hom A A
    _∘_   : ∀ {A B C} → Hom A B → Hom B C → Hom A C
    idˡ   : ∀ {A B} (f : Hom A B) → id A ∘ f ≡ f
    idʳ   : ∀ {A B} (f : Hom A B) → f ∘ id B ≡ f
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D)
             → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

open Category public

------------------------------------------------------------------------
-- Category laws for standard ≤ relation (proven locally)
------------------------------------------------------------------------

-- Left identity: ≤-refl composed with f equals f
≤-idˡ : ∀ {m n} (f : m ≤ n) → ≤-trans ≤-refl f ≡ f
≤-idˡ f = Data.Nat.Properties.≤-irrelevant (≤-trans ≤-refl f) f

-- Right identity: f composed with ≤-refl equals f  
≤-idʳ : ∀ {m n} (f : m ≤ n) → ≤-trans f ≤-refl ≡ f
≤-idʳ f = Data.Nat.Properties.≤-irrelevant (≤-trans f ≤-refl) f

-- Associativity: composition of ≤ proofs is associative
≤-assoc : ∀ {a b c d} (f : a ≤ b) (g : b ≤ c) (h : c ≤ d)
        → ≤-trans (≤-trans f g) h ≡ ≤-trans f (≤-trans g h)
≤-assoc f g h = Data.Nat.Properties.≤-irrelevant 
                  (≤-trans (≤-trans f g) h) 
                  (≤-trans f (≤-trans g h))

------------------------------------------------------------------------
-- CutCat: The temporal spine category
-- Objects = natural numbers (temporal stages)
-- Morphisms = standard ≤ proofs (temporal progression)
------------------------------------------------------------------------

CutCat : Category lzero
CutCat .Obj         = ℕ
CutCat .Hom m n     = m ≤ n          -- Standard Data.Nat.≤
CutCat .id n        = ≤-refl         -- Standard reflexivity
CutCat ._∘_ f g     = ≤-trans f g    -- Standard transitivity
CutCat .idˡ f       = ≤-idˡ f        -- Proven using ≤-irrelevant
CutCat .idʳ f       = ≤-idʳ f        -- Proven using ≤-irrelevant
CutCat .assoc f g h = ≤-assoc f g h  -- Proven using ≤-irrelevant
