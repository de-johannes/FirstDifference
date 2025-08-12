{-# OPTIONS --safe #-}

-- | CutCat: The category of temporal progression
-- | This models how semantic time advances through irreducible distinctions
module Structures.CutCat where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)

------------------------------------------------------------------------
-- Custom temporal ordering: optimized for our semantic time domain
------------------------------------------------------------------------

-- | Our custom ≤ relation for temporal stages
-- | This is cleaner than Data.Nat.≤ for our specific use case
infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n      -- Zero is ≤ any number
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n  -- Successor preserves ≤

-- | Reflexivity: every temporal stage relates to itself
refl≤ : ∀ n → n ≤ n
refl≤ zero    = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

-- | Composition (transitivity): temporal progression is transitive
-- | If time can advance from i to j, and from j to k, 
-- | then it can advance from i to k
infixl 5 _∙_
_∙_ : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
z≤n     ∙ _        = z≤n
s≤s p   ∙ s≤s q    = s≤s (p ∙ q)

-- | Category laws for temporal progression
-- | These prove that our temporal ordering forms a proper category
idʳ-lemma : ∀ {m n} (f : m ≤ n) → f ∙ refl≤ n ≡ f
idʳ-lemma z≤n     = refl
idʳ-lemma (s≤s f) = cong s≤s (idʳ-lemma f)

idˡ-lemma : ∀ {m n} (f : m ≤ n) → refl≤ m ∙ f ≡ f
idˡ-lemma z≤n     = refl
idˡ-lemma (s≤s f) = cong s≤s (idˡ-lemma f)

assoc-∙ : ∀ {a b c d} (f : a ≤ b) (g : b ≤ c) (h : c ≤ d)
        → (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
assoc-∙ z≤n      g        h        = refl
assoc-∙ (s≤s f) (s≤s g) (s≤s h)    = cong s≤s (assoc-∙ f g h)

------------------------------------------------------------------------
-- Generic Category interface
------------------------------------------------------------------------

-- | Abstract definition of a category
record Category (ℓ : Level) : Set (lsuc ℓ) where
  field
    Obj   : Set ℓ                    -- Objects
    Hom   : Obj → Obj → Set ℓ        -- Morphisms between objects
    id    : ∀ A → Hom A A            -- Identity morphism
    _∘_   : ∀ {A B C} → Hom A B → Hom B C → Hom A C  -- Composition
    -- Category laws
    idˡ   : ∀ {A B} (f : Hom A B) → id A ∘ f ≡ f
    idʳ   : ∀ {A B} (f : Hom A B) → f ∘ id B ≡ f
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D)
             → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

open Category public

------------------------------------------------------------------------
-- CutCat: The temporal spine category
------------------------------------------------------------------------

-- | CutCat: Our domain-specific category for temporal progression
-- | Objects are natural numbers (semantic time stages)
-- | Morphisms are temporal advancement proofs
CutCat : Category lzero
CutCat .Obj         = ℕ              -- Time stages as objects
CutCat .Hom m n     = m ≤ n          -- Temporal advancement as morphisms
CutCat .id n        = refl≤ n        -- Identity: staying at same time
CutCat ._∘_ f g     = f ∙ g          -- Composition: chaining advancements
CutCat .idˡ f       = idˡ-lemma f    -- Left identity law
CutCat .idʳ f       = idʳ-lemma f    -- Right identity law  
CutCat .assoc f g h = assoc-∙ f g h  -- Associativity law
