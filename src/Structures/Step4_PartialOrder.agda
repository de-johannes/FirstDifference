{-# OPTIONS --safe #-}

-- Step 4: Drift-induzierte Ordnung
-- Definition: a ≤ᵈ b  :≡  drift a b ≡ a  (komponentenweise Implikation)

module Structures.Step4_PartialOrder where

open import Structures.Step1_BooleanFoundation
open import Structures.Step2_VectorOperations using (Dist; drift; all-true; all-false)
open import Structures.Step3_AlgebraLaws      using (drift-idempotent; drift-comm)

open import Data.Vec                          using (Vec; []; _∷_; zipWith)
open import Data.Bool                         using (Bool; true; false; _∧_)
open import Data.Nat                          using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary                  using (Dec; yes; no)
open import Relation.Nullary.Decidable        using (⌊_⌋)

------------------------------------------------------------------------
-- Hilfslemmata
------------------------------------------------------------------------

-- Entscheidbare Gleichheit für Dist
_≟ᵈ_ : ∀ {n} → (a b : Dist n) → Dec (a ≡ b)
_≟ᵈ_ [] [] = yes refl
_≟ᵈ_ (false ∷ xs) (false ∷ ys) with xs ≟ᵈ ys
... | yes p = yes (cong (false ∷_) p)
... | no ¬p = no λ { refl → ¬p refl }
_≟ᵈ_ (true  ∷ xs) (true  ∷ ys) with xs ≟ᵈ ys
... | yes p = yes (cong (true ∷_) p)
... | no ¬p = no λ { refl → ¬p refl }
_≟ᵈ_ (false ∷ xs) (true  ∷ ys) = no (λ ())
_≟ᵈ_ (true  ∷ xs) (false ∷ ys) = no (λ ())

-- ∧-Identitäten (links sind definitional, rechts via Fallunterscheidung)
∧-trueˡ  : ∀ b → true  ∧ b ≡ b
∧-trueˡ b = refl

∧-falseˡ : ∀ b → false ∧ b ≡ false
∧-falseˡ b = refl

∧-trueʳ  : ∀ b → b ∧ true ≡ b
∧-trueʳ true  = refl
∧-trueʳ false = refl

-- Kopf/Schwanz-Projektionen für Vec (eigene, damit cong darauf anwendbar ist)
headV : ∀ {n} → Vec Bool (suc n) → Bool
headV (x ∷ xs) = x

tailV : ∀ {n} → Vec Bool (suc n) → Vec Bool n
tailV (x ∷ xs) = xs

-- Bool-Transitivität in Implikationsform:
-- x ∧ y ≡ x   und   y ∧ z ≡ y   ⇒   x ∧ z ≡ x
component-trans : ∀ (x y z : Bool) → x ∧ y ≡ x → y ∧ z ≡ y → x ∧ z ≡ x
component-trans false y z xy yz = refl                    -- false ∧ z ≡ false
component-trans true  y z xy yz =
  let y≡true : y ≡ true
      y≡true = trans (sym (∧-trueˡ y)) xy

      step1 : true ∧ z ≡ y ∧ z
      step1 = cong (λ u → u ∧ z) (sym y≡true)

      step2 : true ∧ z ≡ y
      step2 = trans step1 yz

      step3 : true ∧ z ≡ true
      step3 = trans step2 y≡true
  in step3

-- Aus p : zipWith _∧_ (x ∷ xs) (y ∷ ys) ≡ (x ∷ xs)
-- folgt durch Funktionskongruenz:
-- headV p : x ∧ y ≡ x,  tailV p : zipWith _∧_ xs ys ≡ xs
head-of-drift≡a :
  ∀ {n} {x y : Bool} {xs ys : Vec Bool n} →
  zipWith _∧_ (x ∷ xs) (y ∷ ys) ≡ (x ∷ xs) → x ∧ y ≡ x
head-of-drift≡a p = cong headV p

tail-of-drift≡a :
  ∀ {n} {x y : Bool} {xs ys : Vec Bool n} →
  zipWith _∧_ (x ∷ xs) (y ∷ ys) ≡ (x ∷ xs) → zipWith _∧_ xs ys ≡ xs
tail-of-drift≡a p = cong tailV p

------------------------------------------------------------------------
-- Ordnung aus Drift
------------------------------------------------------------------------

_≤ᵈ_ : ∀ {n} → Dist n → Dist n → Set
a ≤ᵈ b = drift a b ≡ a

-- Reflexivität
≤ᵈ-refl : ∀ {n} (a : Dist n) → a ≤ᵈ a
≤ᵈ-refl a = drift-idempotent a

-- Antisymmetrie
≤ᵈ-antisym : ∀ {n} {a b : Dist n} → a ≤ᵈ b → b ≤ᵈ a → a ≡ b
≤ᵈ-antisym {a = a} {b} a≤b b≤a =
  trans (sym a≤b) (trans (drift-comm a b) b≤a)

-- Transitivität (komponentenweise)
≤ᵈ-trans : ∀ {n} {a b c : Dist n} → a ≤ᵈ b → b ≤ᵈ c → a ≤ᵈ c
≤ᵈ-trans {n = zero} {[]} {[]} {[]} refl refl = refl
≤ᵈ-trans {n = suc n} {x ∷ xs} {y ∷ ys} {z ∷ zs} a≤b b≤c =
  let xy≡x : x ∧ y ≡ x
      xy≡x = head-of-drift≡a a≤b

      yz≡y : y ∧ z ≡ y
      yz≡y = head-of-drift≡a b≤c

      head : x ∧ z ≡ x
      head = component-trans x y z xy≡x yz≡y

      tail : zipWith _∧_ xs zs ≡ xs
      tail = ≤ᵈ-trans (tail-of-drift≡a a≤b) (tail-of-drift≡a b≤c)
  in cong₂ _∷_ head tail

------------------------------------------------------------------------
-- Entscheidbarkeit & Schranken
------------------------------------------------------------------------

≤ᵈ-dec : ∀ {n} (a b : Dist n) → Dec (a ≤ᵈ b)
≤ᵈ-dec a b = (drift a b) ≟ᵈ a

≤ᵈ? : ∀ {n} → Dist n → Dist n → Bool
≤ᵈ? a b = ⌊ ≤ᵈ-dec a b ⌋

⊥ᵈ : ∀ {n} → Dist n
⊥ᵈ {n} = all-false n

⊥ᵈ-least : ∀ {n} (a : Dist n) → ⊥ᵈ ≤ᵈ a
⊥ᵈ-least {zero} [] = refl
⊥ᵈ-least {suc n} (x ∷ xs) =
  cong₂ _∷_ (∧-falseˡ x) (⊥ᵈ-least xs)

⊤ᵈ : ∀ {n} → Dist n
⊤ᵈ {n} = all-true n

⊤ᵈ-greatest : ∀ {n} (a : Dist n) → a ≤ᵈ ⊤ᵈ
⊤ᵈ-greatest {zero} [] = refl
⊤ᵈ-greatest {suc n} (x ∷ xs) =
  cong₂ _∷_ (∧-trueʳ x) (⊤ᵈ-greatest xs)

------------------------------------------------------------------------
-- Checks
------------------------------------------------------------------------

example-≤ᵈ :
  (true ∷ false ∷ []) ≤ᵈ (true ∷ true ∷ [])
example-≤ᵈ = refl

example-antisym :
  ∀ (a b : Dist 2) → a ≤ᵈ b → b ≤ᵈ a → a ≡ b
example-antisym a b = ≤ᵈ-antisym

example-trans :
  (false ∷ false ∷ []) ≤ᵈ (true ∷ false ∷ []) →
  (true  ∷ false ∷ []) ≤ᵈ (true ∷ true  ∷ []) →
  (false ∷ false ∷ []) ≤ᵈ (true ∷ true  ∷ [])
example-trans p₁ p₂ =
  ≤ᵈ-trans
    {n = suc (suc zero)}
    {a = false ∷ false ∷ []}
    {b = true  ∷ false ∷ []}
    {c = true  ∷ true  ∷ []}
    p₁ p₂

verify-bottom :
  (false ∷ false ∷ []) ≤ᵈ (true ∷ false ∷ [])
verify-bottom = refl

verify-top :
  (true ∷ false ∷ []) ≤ᵈ (true ∷ true ∷ [])
verify-top = refl

test-decidable :
  Dec ((true ∷ false ∷ []) ≤ᵈ (true ∷ true ∷ []))
test-decidable = ≤ᵈ-dec (true ∷ false ∷ []) (true ∷ true ∷ [])
