module Structures.CutCat where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)

------------------------------------------------------------------------
-- Temporal ordering: foundation for irreversible progression
-- Models the "thin" category of temporal stages
------------------------------------------------------------------------

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

-- Reflexivity: every stage relates to itself
refl≤ : ∀ n → n ≤ n
refl≤ zero    = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

-- Composition (transitivity): temporal progression is transitive
infixl 5 _∙_
_∙_ : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
z≤n     ∙ _        = z≤n
s≤s p   ∙ s≤s q    = s≤s (p ∙ q)

-- Category laws for temporal progression
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
-- CutCat: The temporal spine category
-- Objects = natural numbers (temporal stages)
-- Morphisms = ≤ proofs (temporal progression)
------------------------------------------------------------------------

CutCat : Category lzero
CutCat .Obj         = ℕ
CutCat .Hom m n     = m ≤ n
CutCat .id n        = refl≤ n
CutCat ._∘_ f g     = f ∙ g  -- Note: composition order
CutCat .idˡ f       = idˡ-lemma f
CutCat .idʳ f       = idʳ-lemma f
CutCat .assoc f g h = assoc-∙ f g h
