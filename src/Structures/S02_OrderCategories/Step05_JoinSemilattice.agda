{-# OPTIONS --safe #-}

module Structures.S02_OrderCategories.Step05_JoinSemilattice where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred)
open import Data.Sum using (_⊎_; inj₁; inj₂)

variable
  ℓ : Level
  A : Set ℓ

-- Subset relation
_⊆_ : Pred A ℓ → Pred A ℓ → Set (ℓ ⊔ lsuc ℓ)
P ⊆ Q = ∀ {x} → P x → Q x

-- Extensional equality
_≈_ : Pred A ℓ → Pred A ℓ → Set (ℓ ⊔ lsuc ℓ)
P ≈ Q = (P ⊆ Q) × (Q ⊆ P)

infix 4 _⊆_ _≈_

-- Join (union)
_⊔P_ : Pred A ℓ → Pred A ℓ → Pred A ℓ
(P ⊔P Q) x = P x ⊎ Q x
infixr 6 _⊔P_

-- Canonical injections
left≤join  : ∀ {P Q} → P ⊆ (P ⊔P Q)
left≤join  {P} {Q} p = inj₁ p

right≤join : ∀ {P Q} → Q ⊆ (P ⊔P Q)
right≤join {P} {Q} q = inj₂ q

-- Least upper bound
join-least : ∀ {P Q R} → P ⊆ R → Q ⊆ R → (P ⊔P Q) ⊆ R
join-least p≤r q≤r {x} (inj₁ p) = p≤r p
join-least p≤r q≤r {x} (inj₂ q) = q≤r q

-- Soundness packaging
record IsJoinOf (P Q J : Pred A ℓ) : Set (ℓ ⊔ lsuc ℓ) where
  constructor mkJoin
  field
    leftUB  : P ⊆ J
    rightUB : Q ⊆ J
    least   : ∀ {R} → P ⊆ R → Q ⊆ R → J ⊆ R

open IsJoinOf public

join-soundness : ∀ {P Q} → IsJoinOf P Q (P ⊔P Q)
join-soundness = mkJoin left≤join right≤join join-least

-- Completeness: uniqueness up to ≈
join-completeness : ∀ {P Q J} → IsJoinOf P Q J → J ≈ (P ⊔P Q)
join-completeness j =
  let open IsJoinOf j in
  (least left≤join right≤join , join-least leftUB rightUB)

-- Algebraic laws
join-idem : ∀ {P} → (P ⊔P P) ≈ P
join-idem = (λ {x} {y} → case y of λ where { inj₁ p → p ; inj₂ p → p } , left≤join)

join-comm : ∀ {P Q} → (P ⊔P Q) ≈ (Q ⊔P P)
join-comm = (λ { (inj₁ p) → inj₂ p ; (inj₂ q) → inj₁ q }
           , λ { (inj₁ q) → inj₂ q ; (inj₂ p) → inj₁ p })

join-assoc : ∀ {P Q R} → ((P ⊔P Q) ⊔P R) ≈ (P ⊔P (Q ⊔P R))
join-assoc =
  (λ { (inj₁ (inj₁ p)) → inj₁ p
     ; (inj₁ (inj₂ q)) → inj₂ (inj₁ q)
     ; (inj₂ r)        → inj₂ (inj₂ r) }
  , λ { (inj₁ p)        → inj₁ (inj₁ p)
     ; (inj₂ (inj₁ q)) → inj₁ (inj₂ q)
     ; (inj₂ (inj₂ r)) → inj₂ r })
