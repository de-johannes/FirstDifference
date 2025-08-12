module Structures.CutCat where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)

-- A custom inductive ≤ to keep definitional control (thin, skeletal).
infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}               → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n     → suc m ≤ suc n

-- Reflexivity
refl≤ : ∀ n → n ≤ n
refl≤ zero    = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

-- Transitivity (written as _∙_ to use as categorical composition)
infixl 5 _∙_
_∙_ : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
z≤n       ∙ _          = z≤n
s≤s p     ∙ s≤s q      = s≤s (p ∙ q)

-- Left/right identity w.r.t reflexivity
idʳ-lemma : ∀ {m n} (f : m ≤ n) → f ∙ refl≤ n ≡ f
idʳ-lemma z≤n       = refl
idʳ-lemma (s≤s f)   = cong s≤s (idʳ-lemma f)

idˡ-lemma : ∀ {m n} (f : m ≤ n) → refl≤ m ∙ f ≡ f
idˡ-lemma z≤n       = refl
idˡ-lemma (s≤s f)   = cong s≤s (idˡ-lemma f)

-- Associativity
assoc-lemma
  : ∀ {a b c d} (h : c ≤ d) (g : b ≤ c) (f : a ≤ b)
  → h ∙ (g ∙ f) ≡ (h ∙ g) ∙ f
assoc-lemma z≤n       _          _        = refl
assoc-lemma (s≤s h) (s≤s g) (s≤s f) = cong s≤s (assoc-lemma h g f)

-- A tiny category record sufficient for CutCat.
record Category (ℓ : Level) : Set (lsuc ℓ) where
  field
    Obj   : Set ℓ
    Hom   : Obj → Obj → Set ℓ
    id    : ∀ A → Hom A A
    _∘_   : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    idˡ   : ∀ {A B} (f : Hom A B) → _∘_ (id B) f ≡ f
    idʳ   : ∀ {A B} (f : Hom A B) → _∘_ f (id A) ≡ f
    assoc : ∀ {A B C D} (h : Hom C D) (g : Hom B C) (f : Hom A B)
             → _∘_ h (_∘_ g f) ≡ _∘_ (_∘_ h g) f

open Category public

-- CutCat: objects are ℕ, morphisms are ≤ proofs (thin).
CutCat : Category lzero
CutCat .Obj       = ℕ
CutCat .Hom m n   = m ≤ n
CutCat .id n      = refl≤ n
CutCat ._∘_ g f   = g ∙ f
CutCat .idˡ f     = idʳ-lemma f
CutCat .idʳ f     = idˡ-lemma f
CutCat .assoc h g f = assoc-lemma h g f

-- Optional: explicit isomorphism of thin categories with (ℕ, ≤).
-- TODO: If you later add a Poset→ThinCat functor, show it’s on-the-nose equal.
