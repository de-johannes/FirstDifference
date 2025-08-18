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
-- Meet-Struktur: drift ist größter unterer Schrankenoperator (GLB)
------------------------------------------------------------------------

-- Vektorielle Assoziativität für drift (zipWith _∧_)
-- nutzt ∧-assoc aus Step1_BooleanFoundation
drift-assoc : ∀ {n} → (a b c : Dist n) → drift (drift a b) c ≡ drift a (drift b c)
drift-assoc {zero} [] [] [] = refl
drift-assoc {suc n} (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (∧-assoc x y z) (drift-assoc xs ys zs)

-- Projektionen: a ∧ b ≤ a  und  a ∧ b ≤ b
meet≤₁ : ∀ {n} (a b : Dist n) → drift a b ≤ᵈ a
meet≤₁ a b =
  -- Ziel: drift (drift a b) a ≡ drift a b
  let s₁ = drift-assoc a b a
      s₂ = cong (λ t → drift a t) (drift-comm b a)
      s₃ = sym (drift-assoc a a b)
      s₄ = cong (λ t → drift t b) (drift-idempotent a)
  in trans s₁ (trans s₂ (trans s₃ s₄))

-- Projektion 2: a ∧ b ≤ b
meet≤₂ : ∀ {n} (a b : Dist n) → drift a b ≤ᵈ b
meet≤₂ a b =
  -- drift (drift a b) b
  --   ≡ drift (drift b a) b           (cong mit drift-comm a b)
  --   ≡ drift b a                     (meet≤₁ b a)
  --   ≡ drift a b                     (sym (drift-comm a b))
  let s₁ = cong (λ t → drift t b) (drift-comm a b)
      s₂ = meet≤₁ b a
      s₃ = sym (drift-comm a b)
  in trans s₁ (trans s₂ s₃)

-- Größter unterer Schranken:  c ≤ a  ∧  c ≤ b  ⇒  c ≤ (a ∧ b)
glb-≤ᵈ : ∀ {n} {a b c : Dist n} → c ≤ᵈ a → c ≤ᵈ b → c ≤ᵈ drift a b
glb-≤ᵈ {a = a} {b} {c} c≤a c≤b =
  -- Ziel: drift c (drift a b) ≡ c
  -- Umformen: ≡ (drift (drift c a) b)  ≡ (drift c b)  ≡ c
  let t₁ = sym (drift-assoc c a b)
      t₂ = cong (λ t → drift t b) c≤a
      t₃ = c≤b
  in trans t₁ (trans t₂ t₃)

------------------------------------------------------------------------
-- Absorptionsgesetze:  a ∧ (a ∨ b) = a  und  a ∨ (a ∧ b) = a
-- (komponentenweise; hier ∧ ≡ drift, ∨ ≡ join)
------------------------------------------------------------------------

open import Structures.Step2_VectorOperations using (join; neg)

-- Bool-Absorption
∨-absorb-∧ : ∀ (a b : Bool) → a ∨ (a ∧ b) ≡ a
∨-absorb-∧ false b = refl
∨-absorb-∧ true  b = refl

∧-absorb-∨ : ∀ (a b : Bool) → a ∧ (a ∨ b) ≡ a
∧-absorb-∨ false b = refl
∧-absorb-∨ true  b = refl

-- Vektoriell (komponentenweise via zipWith)
absorb-∨-∧ : ∀ {n} (a b : Dist n) → join a (drift a b) ≡ a
absorb-∨-∧ {zero} []       []       = refl
absorb-∨-∧ {suc n} (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (∨-absorb-∧ x y) (absorb-∨-∧ xs ys)

absorb-∧-∨ : ∀ {n} (a b : Dist n) → drift a (join a b) ≡ a
absorb-∧-∨ {zero} []       []       = refl
absorb-∧-∨ {suc n} (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (∧-absorb-∨ x y) (absorb-∧-∨ xs ys)

------------------------------------------------------------------------
-- Komplement-Gesetze (mit neg = map not):  a ∧ ¬a = ⊥,  a ∨ ¬a = ⊤
-- sowie De-Morgan-Regeln
------------------------------------------------------------------------

-- Bool-Einzelfakten
∧-not-false : ∀ a → a ∧ not a ≡ false
∧-not-false false = refl
∧-not-false true  = refl

∨-not-true : ∀ a → a ∨ not a ≡ true
∨-not-true false = refl
∨-not-true true  = refl

-- Vektoriell (nutzt ⊥ᵈ/⊤ᵈ aus Step 4)
compl-meet-bot : ∀ {n} (a : Dist n) → drift a (neg a) ≡ ⊥ᵈ
compl-meet-bot {zero} []       = refl
compl-meet-bot {suc n} (x ∷ xs) =
  cong₂ _∷_ (∧-not-false x) (compl-meet-bot xs)

compl-join-top : ∀ {n} (a : Dist n) → join a (neg a) ≡ ⊤ᵈ
compl-join-top {zero} []       = refl
compl-join-top {suc n} (x ∷ xs) =
  cong₂ _∷_ (∨-not-true x) (compl-join-top xs)

-- De Morgan: ¬(a ∧ b) = ¬a ∨ ¬b  und  ¬(a ∨ b) = ¬a ∧ ¬b
deMorgan₁ : ∀ {n} (a b : Dist n) → neg (drift a b) ≡ join (neg a) (neg b)
deMorgan₁ {zero} []       []       = refl
deMorgan₁ {suc n} (x ∷ xs) (y ∷ ys) =
  -- not (x ∧ y) ≡ (not x) ∨ (not y), komponentenweise
  cong₂ _∷_ refl (deMorgan₁ xs ys)

deMorgan₂ : ∀ {n} (a b : Dist n) → neg (join a b) ≡ drift (neg a) (neg b)
deMorgan₂ {zero} []       []       = refl
deMorgan₂ {suc n} (x ∷ xs) (y ∷ ys) =
  -- not (x ∨ y) ≡ (not x) ∧ (not y), komponentenweise
  cong₂ _∷_ refl (deMorgan₂ xs ys)

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
