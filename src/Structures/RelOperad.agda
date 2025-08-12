module Structures.RelOperad where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin)

-- Signature: n-ary relation constructors as abstract operations.
record RelOperad (ℓ : Level) : Set (lsuc ℓ) where
  field
    O     : ℕ → Set ℓ                          -- operations by arity
    η     : O 1                                 -- unit (identity relation)
    γ     : ∀ {n} → O n → (∀ (i : Fin n) → O 1) → O 1  -- unary target for now
    unitL : ∀ {n} (o : O n) → γ o (λ _ → η) ≡ η
    unitR :           γ η (λ _ → η) ≡ η
    assoc : ∀ {n} (o : O n)
              (q : ∀ (i : Fin n) → O 1)
              (r : ∀ (_ : Fin 1) → O 1)
            → γ (γ o q) r ≡ γ o (λ i → γ (q i) r)

-- A toy instance (enough to compile; we’ll refine semantics later).
ToyRelOperad : RelOperad lzero
ToyRelOperad .RelOperad.O     = λ _ → ⊤
ToyRelOperad .RelOperad.η     = tt
ToyRelOperad .RelOperad.γ _ _ = tt
ToyRelOperad .RelOperad.unitL _ = refl
ToyRelOperad .RelOperad.unitR   = refl
ToyRelOperad .RelOperad.assoc _ _ _ = refl
