{-# OPTIONS --safe #-}

-- | Step 04: Drift-Induced Partial Order
-- |
-- | Definition:
-- |   a ≤ᵈ b  :≡  drift a b ≡ a   (componentwise implication)
-- |
-- | Purpose:
-- |   Define and verify that ≤ᵈ is a partial order on distinction vectors.
-- |   Show that drift is the greatest lower bound (GLB, meet)
-- |   and join is the least upper bound (LUB, join).
-- |
-- | Method:
-- |   Structural induction on vectors, combined with Boolean laws
-- |   from Step01–Step03. No axioms or postulates, --safe throughout.
-- |
-- | Guarantee:
-- |   ≤ᵈ is reflexive, antisymmetric, and transitive.
-- |   ⊥ᵈ and ⊤ᵈ exist as least/greatest elements.
-- |   Drift/join form a bounded lattice structure.

module Structures.S02_OrderCategories.Step04_PartialOrder where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; zipWith)

-- Scalar Booleans and laws (ours)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Soundness
  using (∧-assoc; ∧-comm; ∧-identityʳ; ∧-idem; ∧-zeroʳ)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation_Completeness
  using (∧-identityˡ; ∧-zeroˡ; ∧-complement; ∨-complement; DeMorgan-∧∨; DeMorgan-∨∧)

-- Distinction vectors and vector laws
open import Structures.S01_BooleanCore.Step02_VectorOperations
  using (Dist; drift; join; neg; all-true; all-false)
open import Structures.S01_BooleanCore.Step02_VectorOperations_Soundness
  using (drift-assoc; drift-comm; drift-identityʳ; drift-zeroʳ; join-assoc; join-comm)
open import Structures.S01_BooleanCore.Step03_AlgebraLaws_Soundness
  using ( sound-drift-idempotent
        ; sound-drift-identityˡ; sound-drift-zeroˡ; sound-drift-absorb
        ; sound-join-idempotent; sound-join-identityʳ; sound-join-identityˡ
        ; sound-join-oneʳ; sound-join-oneˡ; sound-join-absorb
        ; sound-drift-join-distrib-right; sound-join-drift-distrib-right )

------------------------------------------------------------------------
-- Vector utilities
------------------------------------------------------------------------

headV : ∀ {n A} → Vec A (suc n) → A
headV (x ∷ xs) = x

tailV : ∀ {n A} → Vec A (suc n) → Vec A n
tailV (x ∷ xs) = xs

------------------------------------------------------------------------
-- Definition: Partial Order
------------------------------------------------------------------------

_≤ᵈ_ : ∀ {n} → Dist n → Dist n → Set
a ≤ᵈ b = drift a b ≡ a

-- Reflexivity
≤ᵈ-refl : ∀ {n} (a : Dist n) → a ≤ᵈ a
≤ᵈ-refl a = sound-drift-idempotent a

-- Antisymmetry
≤ᵈ-antisym : ∀ {n} {a b : Dist n} → a ≤ᵈ b → b ≤ᵈ a → a ≡ b
≤ᵈ-antisym {a = a} {b} a≤b b≤a =
  trans (sym a≤b) (trans (drift-comm a b) b≤a)

-- Transitivity
≤ᵈ-trans : ∀ {n} {a b c : Dist n} → a ≤ᵈ b → b ≤ᵈ c → a ≤ᵈ c
≤ᵈ-trans {n = zero} {[]} {[]} {[]} refl refl = refl
≤ᵈ-trans {n = suc n} {x ∷ xs} {y ∷ ys} {z ∷ zs} a≤b b≤c =
  cong₂ _∷_ head tail
  where
    xy≡x : x ∧ y ≡ x
    xy≡x = cong headV a≤b

    yz≡y : y ∧ z ≡ y
    yz≡y = cong headV b≤c

    -- helper: if x∧y≡x and y∧z≡y then x∧z≡x
    helper : ∀ (x y z : Bool) → x ∧ y ≡ x → y ∧ z ≡ y → x ∧ z ≡ x
    helper false y z _      _      = refl
    helper true  y z xy≡x  yz≡y =
      let
        y≡true = trans (sym (∧-identityˡ y)) xy≡x
        step1  = cong (λ u → u ∧ z) (sym y≡true)
        step2  = trans step1 yz≡y
      in trans step2 y≡true

    head : x ∧ z ≡ x
    head = helper x y z xy≡x yz≡y

    tail : zipWith _∧_ xs zs ≡ xs
    tail = ≤ᵈ-trans (cong tailV a≤b) (cong tailV b≤c)

------------------------------------------------------------------------
-- Decidability and bounds
------------------------------------------------------------------------

_≟ᵈ_ : ∀ {n} → (a b : Dist n) → Dec (a ≡ b)
_≟ᵈ_ [] [] = yes refl
_≟ᵈ_ (false ∷ xs) (false ∷ ys) with xs ≟ᵈ ys
... | yes p = yes (cong (false ∷_) p)
... | no ¬p = no λ { refl → ¬p refl }
_≟ᵈ_ (true ∷ xs) (true ∷ ys) with xs ≟ᵈ ys
... | yes p = yes (cong (true ∷_) p)
... | no ¬p = no λ { refl → ¬p refl }
_≟ᵈ_ (false ∷ xs) (true  ∷ ys) = no (λ ())
_≟ᵈ_ (true  ∷ xs) (false ∷ ys) = no (λ ())

≤ᵈ-dec : ∀ {n} (a b : Dist n) → Dec (a ≤ᵈ b)
≤ᵈ-dec a b = (drift a b) ≟ᵈ a

-- Convert Dec to OUR Bool
fromDec : ∀ {P : Set} → Dec P → Bool
fromDec (yes _) = true
fromDec (no  _) = false

≤ᵈ? : ∀ {n} → Dist n → Dist n → Bool
≤ᵈ? a b = fromDec (≤ᵈ-dec a b)

⊥ᵈ : ∀ {n} → Dist n
⊥ᵈ {n} = all-false n

⊥ᵈ-least : ∀ {n} (a : Dist n) → ⊥ᵈ ≤ᵈ a
⊥ᵈ-least {zero} [] = refl
⊥ᵈ-least {suc n} (x ∷ xs) =
  cong₂ _∷_ (∧-zeroˡ x) (⊥ᵈ-least xs)

⊤ᵈ : ∀ {n} → Dist n
⊤ᵈ {n} = all-true n

⊤ᵈ-greatest : ∀ {n} (a : Dist n) → a ≤ᵈ ⊤ᵈ
⊤ᵈ-greatest {zero} [] = refl
⊤ᵈ-greatest {suc n} (x ∷ xs) =
  cong₂ _∷_ (∧-identityʳ x) (⊤ᵈ-greatest xs)

------------------------------------------------------------------------
-- Meet: drift as GLB
------------------------------------------------------------------------

meet≤₁ : ∀ {n} (a b : Dist n) → drift a b ≤ᵈ a
meet≤₁ a b =
  let s₁ = drift-assoc a b a
      s₂ = cong (λ t → drift a t) (drift-comm b a)
      s₃ = sym (drift-assoc a a b)
      s₄ = cong (λ t → drift t b) (sound-drift-idempotent a)
  in trans s₁ (trans s₂ (trans s₃ s₄))

meet≤₂ : ∀ {n} (a b : Dist n) → drift a b ≤ᵈ b
meet≤₂ a b =
  let s₁ = cong (λ t → drift t b) (drift-comm a b)
      s₂ = meet≤₁ b a
      s₃ = sym (drift-comm a b)
  in trans s₁ (trans s₂ s₃)

glb-≤ᵈ : ∀ {n} {a b c : Dist n} → c ≤ᵈ a → c ≤ᵈ b → c ≤ᵈ drift a b
glb-≤ᵈ {a = a} {b} {c} c≤a c≤b =
  let t₁ = sym (drift-assoc c a b)
      t₂ = cong (λ t → drift t b) c≤a
      t₃ = c≤b
  in trans t₁ (trans t₂ t₃)

------------------------------------------------------------------------
-- Join: join as LUB
------------------------------------------------------------------------

ub-join₁ : ∀ {n} (a b : Dist n) → a ≤ᵈ join a b
ub-join₁ a b = sound-drift-absorb a b

ub-join₂ : ∀ {n} (a b : Dist n) → b ≤ᵈ join a b
ub-join₂ a b =
  let s = cong (λ t → drift b t) (join-comm a b)
  in trans s (sound-drift-absorb b a)

lub-≤ᵈ : ∀ {n} {a b c : Dist n} → a ≤ᵈ c → b ≤ᵈ c → join a b ≤ᵈ c
lub-≤ᵈ {a = a} {b} {c} a≤c b≤c =
  let d₁ = sound-drift-join-distrib-right a b c
      d₂ = cong₂ join a≤c b≤c
  in trans d₁ d₂

------------------------------------------------------------------------
-- Complements & De Morgan (vector form)
------------------------------------------------------------------------

compl-meet-bot : ∀ {n} (a : Dist n) → drift a (neg a) ≡ all-false n
compl-meet-bot {zero} []       = refl
compl-meet-bot {suc n} (x ∷ xs) =
  cong₂ _∷_ (∧-complement x) (compl-meet-bot xs)

compl-join-top : ∀ {n} (a : Dist n) → join a (neg a) ≡ all-true n
compl-join-top {zero} []       = refl
compl-join-top {suc n} (x ∷ xs) =
  cong₂ _∷_ (∨-complement x) (compl-join-top xs)

deMorgan₁ : ∀ {n} (a b : Dist n) → neg (drift a b) ≡ join (neg a) (neg b)
deMorgan₁ {zero} []       []       = refl
deMorgan₁ {suc n} (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (DeMorgan-∧∨ x y) (deMorgan₁ xs ys)

deMorgan₂ : ∀ {n} (a b : Dist n) → neg (join a b) ≡ drift (neg a) (neg b)
deMorgan₂ {zero} []       []       = refl
deMorgan₂ {suc n} (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (DeMorgan-∨∧ x y) (deMorgan₂ xs ys)