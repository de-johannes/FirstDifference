{-# OPTIONS --safe #-}

module code where

------------------------------------------------------------------------
-- FOUNDATIONAL MATHEMATICAL PRIMITIVES
-- 
-- We define everything from scratch to ensure complete self-containment
-- and compatibility with Agda's --safe flag. This supports the philosophical
-- claim that the first distinction D₀ requires no external assumptions.
------------------------------------------------------------------------

-- Propositional equality: the most basic notion of sameness
infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x  -- Every object is equal to itself

-- Basic properties of equality
sym : ∀ {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

cong : ∀ {A B : Set}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set}{x y : A}{u v : B} → (f : A → B → C) → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

-- The empty type: represents impossibility/contradiction
data ⊥ : Set where

-- Negation: A is false iff assuming A leads to contradiction
¬_ : Set → Set
¬ A = A → ⊥

-- Natural numbers: the foundation of discrete mathematics
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- Boolean type: the minimal distinction between two states
-- This directly models the binary nature of the first distinction D₀
data Bool : Set where 
  false true : Bool

-- Boolean conjunction: models the "drift" operation
-- Key insight: false ∧ x = false (false "absorbs" everything)
--             true ∧ x = x (true acts as identity)
_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

-- Length-indexed vectors: the mathematical structure for distinctions
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero                                    -- empty vector
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)          -- cons operation

-- Componentwise application of a binary function to two vectors
zipWith : ∀ {n A B C} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith f []       []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

-- Vector accessors (needed for monotonicity proofs)
head : ∀ {n A} → Vec A (suc n) → A
head (x ∷ _) = x

tail : ∀ {n A} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

------------------------------------------------------------------------
-- BOOLEAN ALGEBRA LAWS
--
-- These are proved by exhaustive case analysis, demonstrating that 
-- Boolean logic emerges necessarily from the binary distinction.
-- Each proof covers all possible combinations of inputs.
------------------------------------------------------------------------

-- Commutativity: order doesn't matter in logical conjunction
∧-comm : ∀ a b → a ∧ b ≡ b ∧ a
∧-comm true  true  = refl  -- true ∧ true = true = true ∧ true
∧-comm true  false = refl  -- true ∧ false = false = false ∧ true  
∧-comm false true  = refl  -- false ∧ true = false = true ∧ false
∧-comm false false = refl  -- false ∧ false = false = false ∧ false

-- Associativity: grouping doesn't matter in logical conjunction
∧-assoc : ∀ a b c → a ∧ (b ∧ c) ≡ (a ∧ b) ∧ c
∧-assoc true  b c = refl  -- When a=true, both sides equal b∧c
∧-assoc false b c = refl  -- When a=false, both sides equal false

-- Idempotence: repeating the same input doesn't change the result
∧-idem : ∀ a → a ∧ a ≡ a
∧-idem true  = refl  -- true ∧ true = true
∧-idem false = refl  -- false ∧ false = false

------------------------------------------------------------------------
-- THE TOKEN PRINCIPLE AND IRREFUTABILITY OF D₀
--
-- This formalizes the core philosophical claim: any token instantiation
-- necessarily brings about the first distinction D₀. The irrefutability
-- theorem shows that denying D₀ is self-defeating.
------------------------------------------------------------------------

-- The Token Principle as a formal structure
record TokenPrinciple : Set₁ where
  field
    D0       : Set                    -- The first distinction
    Token    : Set                    -- The type of realizable tokens  
    token    : Token                  -- Evidence that tokens exist
    token⇒D0 : Token → D0             -- Any token instantiates D₀
open TokenPrinciple public

-- Irrefutability theorem: denying D₀ leads to contradiction
-- Proof: To deny D₀, one must express the denial, which requires a token,
-- which by the Token Principle instantiates D₀, contradicting the denial.
irrefutable : (TP : TokenPrinciple) → ¬ (D0 TP) → ⊥
irrefutable TP notD0 = notD0 (token⇒D0 TP (token TP))

------------------------------------------------------------------------
-- DISTINCTION VECTORS AND THE DRIFT OPERATION
--
-- From the first distinction D₀, we construct n-dimensional distinction
-- spaces. The "drift" operation models how distinctions interact.
------------------------------------------------------------------------

-- An n-dimensional distinction is a vector of n Boolean values
-- Each component represents a binary distinction in that dimension
Dist : ℕ → Set
Dist n = Vec Bool n

-- The drift operation: componentwise Boolean conjunction
-- Philosophical interpretation: the "intersection" of two distinction states
drift : ∀ {n} → Dist n → Dist n → Dist n
drift = zipWith _∧_

------------------------------------------------------------------------
-- ALGEBRAIC LAWS FOR DISTINCTION VECTORS
--
-- These proofs show how the Boolean laws "lift" to vector operations
-- through structural induction. This demonstrates the scalability of
-- the foundational distinctions.
------------------------------------------------------------------------

-- Commutativity of drift: order doesn't matter in distinction intersection
drift-comm : ∀ {n} (x y : Dist n) → drift x y ≡ drift y x
drift-comm [] [] = refl                                    -- Base case: empty vectors
drift-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_                  -- Inductive case:
  (∧-comm x y)                                             -- - heads commute by Boolean law
  (drift-comm xs ys)                                       -- - tails commute by induction

-- Associativity of drift: grouping doesn't matter in distinction intersection  
drift-assoc : ∀ {n} (x y z : Dist n) → drift x (drift y z) ≡ drift (drift x y) z
drift-assoc [] [] [] = refl                                -- Base case: empty vectors
drift-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_       -- Inductive case:
  (∧-assoc x y z)                                          -- - heads associate by Boolean law
  (drift-assoc xs ys zs)                                   -- - tails associate by induction

-- Idempotence of drift: intersecting with itself yields the same distinction
drift-idem : ∀ {n} (x : Dist n) → drift x x ≡ x
drift-idem [] = refl                                       -- Base case: empty vectors
drift-idem (x ∷ xs) = cong₂ _∷_                           -- Inductive case:
  (∧-idem x)                                               -- - heads idempotent by Boolean law
  (drift-idem xs)                                          -- - tails idempotent by induction

------------------------------------------------------------------------
-- THE EMERGENT PARTIAL ORDER
--
-- From the algebraic structure, a natural ordering emerges.
-- This order has deep philosophical significance: it represents
-- the hierarchical relationship between distinction states.
------------------------------------------------------------------------

-- The drift-based partial order: x ≤ᴰ y means "x is absorbed by y"
infix 4 _≤ᴰ_
_≤ᴰ_ : ∀ {n} → Dist n → Dist n → Set
x ≤ᴰ y = drift x y ≡ x

-- Reflexivity: every distinction is related to itself
refl-≤ᴰ : ∀ {n} (x : Dist n) → x ≤ᴰ x
refl-≤ᴰ = drift-idem

-- Transitivity: the order relation chains correctly
-- Proof uses the algebraic properties of drift
trans-≤ᴰ : ∀ {n}{x y z : Dist n} → x ≤ᴰ y → y ≤ᴰ z → x ≤ᴰ z
trans-≤ᴰ {x = x} {y} {z} xy yz = 
  trans (cong (λ w → drift w z) (sym xy))                  -- drift x z = drift (drift x y) z
       (trans (sym (drift-assoc x y z))                    -- = drift x (drift y z)
              (trans (cong (drift x) yz) xy))              -- = drift x y = x

-- Antisymmetry: mutual ordering implies equality
antisym-≤ᴰ : ∀ {n}{x y : Dist n} → x ≤ᴰ y → y ≤ᴰ x → x ≡ y
antisym-≤ᴰ {x = x} {y} xy yx = 
  trans (sym xy)                                           -- x = drift x y
       (trans (drift-comm x y) yx)                         -- = drift y x = y

------------------------------------------------------------------------
-- MONOTONICITY AND ADVANCED PROPERTIES
--
-- These proofs establish that the drift operation respects the ordering.
-- The complexity here demonstrates the rich structure that emerges from
-- the simple foundational distinction.
------------------------------------------------------------------------

-- Helper lemmas for working with vector equality
cong-head : ∀ {n A} {x y : Vec A (suc n)} → x ≡ y → head x ≡ head y
cong-head refl = refl

cong-tail : ∀ {n A} {x y : Vec A (suc n)} → x ≡ y → tail x ≡ tail y
cong-tail refl = refl

-- Boolean-level monotonicity: the core technical lemma
-- This proves by exhaustive case analysis that ∧ preserves the absorption order
-- Cases marked with () are impossible because they violate the premise
∧-mono-bool : ∀ {a b c d : Bool} → (a ∧ b ≡ a) → (c ∧ d ≡ c) → ((a ∧ c) ∧ (b ∧ d) ≡ (a ∧ c))

-- When a=true, b=true (first premise satisfied: true ∧ true = true)
∧-mono-bool {true}  {true}  {true}  {true}  _ _ = refl     -- All true: straightforward
∧-mono-bool {true}  {true}  {true}  {false} _ ()          -- Second premise fails: true ∧ false ≠ true
∧-mono-bool {true}  {true}  {false} {true}  _ _ = refl     -- Works: all operations yield false
∧-mono-bool {true}  {true}  {false} {false} _ _ = refl     -- Works: all operations yield false

-- When a=true, b=false (first premise fails: true ∧ false ≠ true)
∧-mono-bool {true}  {false} {true}  {true}  () _          -- First premise impossible
∧-mono-bool {true}  {false} {true}  {false} () ()         -- Both premises impossible
∧-mono-bool {true}  {false} {false} {true}  () _          -- First premise impossible
∧-mono-bool {true}  {false} {false} {false} () _          -- First premise impossible

-- When a=false (first premise satisfied: false ∧ x = false for any x)
∧-mono-bool {false} {true}  {true}  {true}  _ _ = refl     -- All operations work correctly
∧-mono-bool {false} {true}  {true}  {false} _ ()          -- Second premise fails
∧-mono-bool {false} {true}  {false} {true}  _ _ = refl     -- Works: false absorbs everything
∧-mono-bool {false} {true}  {false} {false} _ _ = refl     -- Works: false absorbs everything
∧-mono-bool {false} {false} {true}  {true}  _ _ = refl     -- Works: false absorbs everything  
∧-mono-bool {false} {false} {true}  {false} _ ()          -- Second premise fails
∧-mono-bool {false} {false} {false} {true}  _ _ = refl     -- Works: false absorbs everything
∧-mono-bool {false} {false} {false} {false} _ _ = refl     -- Works: false absorbs everything

-- Vector-level monotonicity: drift respects the partial order
-- This is the key theorem showing that the emergent structure is well-behaved
drift-mono : ∀ {n}{x₁ x₂ y₁ y₂ : Dist n} → x₁ ≤ᴰ x₂ → y₁ ≤ᴰ y₂ → drift x₁ y₁ ≤ᴰ drift x₂ y₂

-- Base case: empty vectors (explicit pattern matching resolves type inference issues)
drift-mono {zero} {[]} {[]} {[]} {[]} _ _ = refl

-- Inductive case: non-empty vectors  
drift-mono {suc n} {x₁ ∷ xs₁} {x₂ ∷ xs₂} {y₁ ∷ ys₁} {y₂ ∷ ys₂} x₁≤x₂ y₁≤y₂ = 
  cong₂ _∷_                                                -- Combine head and tail proofs
    (∧-mono-bool (cong-head x₁≤x₂) (cong-head y₁≤y₂))    -- Head: use Boolean monotonicity
    (drift-mono (cong-tail x₁≤x₂) (cong-tail y₁≤y₂))     -- Tail: use inductive hypothesis

------------------------------------------------------------------------
-- CONCLUSION
--
-- This formalization demonstrates that from the minimal assumption of 
-- the Token Principle, an entire algebraic structure emerges necessarily.
-- The first distinction D₀ is not only irrefutable but generative:
-- it gives rise to Boolean algebra, vector operations, partial orders,
-- and monotonicity properties.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Constants: ⊥ᴰ (all false) and ⊤ᴰ (all true)
------------------------------------------------------------------------

replicate : ∀ {A : Set}{n : ℕ} → A → Vec A n
replicate {n = zero}  a = []
replicate {n = suc n} a = a ∷ replicate a

⊥ᴰ : ∀ n → Dist n
⊥ᴰ n = replicate false

⊤ᴰ : ∀ n → Dist n
⊤ᴰ n = replicate true

------------------------------------------------------------------------
-- Absorption/Identity of drift
------------------------------------------------------------------------

drift-bottom-right : ∀ {n} (x : Dist n) → drift x (⊥ᴰ n) ≡ ⊥ᴰ n
drift-bottom-right {zero}  []        = refl
drift-bottom-right {suc n} (true  ∷ xs) = cong₂ _∷_ refl (drift-bottom-right xs)
drift-bottom-right {suc n} (false ∷ xs) = cong₂ _∷_ refl (drift-bottom-right xs)

drift-bottom-left : ∀ {n} (x : Dist n) → drift (⊥ᴰ n) x ≡ (⊥ᴰ n)
drift-bottom-left {zero}  []        = refl
drift-bottom-left {suc n} (_ ∷ xs)  = cong₂ _∷_ refl (drift-bottom-left xs)

drift-top-right : ∀ {n} (x : Dist n) → drift x (⊤ᴰ n) ≡ x
drift-top-right {zero}  []        = refl
drift-top-right {suc n} (true  ∷ xs) = cong₂ _∷_ refl (drift-top-right xs)
drift-top-right {suc n} (false ∷ xs) = cong₂ _∷_ refl (drift-top-right xs)

drift-top-left : ∀ {n} (x : Dist n) → drift (⊤ᴰ n) x ≡ x
drift-top-left {zero}  []        = refl
drift-top-left {suc n} (_ ∷ xs)  = cong₂ _∷_ refl (drift-top-left xs)

------------------------------------------------------------------------
-- Order statements: ⊥ᴰ is the least, ⊤ᴰ the greatest element
------------------------------------------------------------------------

bottom-least : ∀ {n} (x : Dist n) → (⊥ᴰ n) ≤ᴰ x
bottom-least x = drift-bottom-left x  -- drift (⊥) x ≡ ⊥

top-greatest : ∀ {n} (x : Dist n) → x ≤ᴰ (⊤ᴰ n)
top-greatest x = drift-top-right x     -- drift x (⊤) ≡ x

------------------------------------------------------------------------
-- "No illogic": Drift is always ≤ its parents (monotone descent)
------------------------------------------------------------------------

drift≤left : ∀ {n} (x y : Dist n) → drift x y ≤ᴰ x
drift≤left x y =
  -- (x ∧ y) ∧ x ≡ x ∧ y
  trans (sym (drift-assoc x y x))
       (trans (cong (drift x) (drift-comm y x))
              (trans (drift-assoc x x y)
                     (cong (λ v → drift v y) (drift-idem x))))

drift≤right : ∀ {n} (x y : Dist n) → drift x y ≤ᴰ y
drift≤right x y =
  -- (x ∧ y) ∧ y ≡ x ∧ (y ∧ y) ≡ x ∧ y
  trans (sym (drift-assoc x y y))
       (cong (drift x) (drift-idem y))
