-- src/Step3_AlgebraLaws.agda  
{-# OPTIONS --safe #-}

-- | Step 3: Vector Algebra Laws via Boolean Property Lifting
-- | Proof: n-dimensional Boolean algebra from 1-dimensional laws
module Structures.Step3_AlgebraLaws where

open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Structures.S01_BooleanCore.Step01_BooleanFoundation
open import Structures.S01_BooleanCore.Step02_VectorOperations

------------------------------------------------------------------------
-- LIFTING STRATEGY: Boolean laws → Vector laws
------------------------------------------------------------------------

-- | Drift associativity: lifts ∧-assoc to vectors
drift-assoc : ∀ {n} (a b c : Dist n) → 
              drift (drift a b) c ≡ drift a (drift b c)
drift-assoc []       []       []       = refl
drift-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = 
  cong₂ _∷_ (∧-assoc x y z) (drift-assoc xs ys zs)

-- | Drift commutativity: lifts ∧-comm to vectors  
drift-comm : ∀ {n} (a b : Dist n) → drift a b ≡ drift b a
drift-comm []       []       = refl  
drift-comm (x ∷ xs) (y ∷ ys) = 
  cong₂ _∷_ (∧-comm x y) (drift-comm xs ys)

-- | Drift identity: lifts ∧-identityʳ to vectors
drift-identity : ∀ {n} (d : Dist n) → drift d (all-true n) ≡ d
drift-identity []       = refl
drift-identity (x ∷ xs) = 
  cong₂ _∷_ (∧-identityʳ x) (drift-identity xs)

-- | Drift idempotence: lifts ∧-idem to vectors
drift-idempotent : ∀ {n} (a : Dist n) → drift a a ≡ a
drift-idempotent []       = refl
drift-idempotent (x ∷ xs) = 
  cong₂ _∷_ (∧-idem x) (drift-idempotent xs)

-- | Drift absorption: lifts ∧-zeroʳ to vectors
drift-absorbing : ∀ {n} (d : Dist n) → drift d (all-false n) ≡ all-false n
drift-absorbing []       = refl
drift-absorbing (x ∷ xs) = 
  cong₂ _∷_ (∧-zeroʳ x) (drift-absorbing xs)

------------------------------------------------------------------------
-- MATHEMATICAL VICTORY: Vec Bool n forms Boolean Algebra!
-- Component-wise operations preserve all algebraic structure
------------------------------------------------------------------------

-- Ergänzungen für Join (∨) und Distributivität
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Structures.Step2_VectorOperations using (Dist; drift; join)

-- Lokale Bool-Lemmata (Step 1 liefert ∨-comm, aber nicht diese hier)
∨-assoc : ∀ (x y z : Bool) → (x ∨ y) ∨ z ≡ x ∨ (y ∨ z)
∨-assoc false y z = refl
∨-assoc true  y z = refl

∨-idem  : ∀ (x : Bool) → x ∨ x ≡ x
∨-idem false = refl
∨-idem true  = refl

-- Distributivität: (x ∨ y) ∧ z ≡ (x ∧ z) ∨ (y ∧ z)
∧-dist-∨ʳ : ∀ (x y z : Bool) → (x ∨ y) ∧ z ≡ (x ∧ z) ∨ (y ∧ z)
∧-dist-∨ʳ true  true  true  = refl
∧-dist-∨ʳ true  true  false = refl
∧-dist-∨ʳ true  false true  = refl
∧-dist-∨ʳ true  false false = refl
∧-dist-∨ʳ false true  true  = refl
∧-dist-∨ʳ false true  false = refl
∧-dist-∨ʳ false false true  = refl
∧-dist-∨ʳ false false false = refl

-- Lifts auf Dist (nutzen ∨-comm aus Step 1!)
join-assoc : ∀ {n} (a b c : Dist n) → join (join a b) c ≡ join a (join b c)
join-assoc [] [] [] = refl
join-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (∨-assoc x y z) (join-assoc xs ys zs)

join-comm : ∀ {n} (a b : Dist n) → join a b ≡ join b a
join-comm [] [] = refl
join-comm (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (∨-comm x y) (join-comm xs ys)

join-idempotent : ∀ {n} (a : Dist n) → join a a ≡ a
join-idempotent [] = refl
join-idempotent (x ∷ xs) =
  cong₂ _∷_ (∨-idem x) (join-idempotent xs)

-- Distributivität auf Dist:
-- drift (join a b) c  ≡  join (drift a c) (drift b c)
drift-join-distrib-right : ∀ {n} (a b c : Dist n) →
  drift (join a b) c ≡ join (drift a c) (drift b c)
drift-join-distrib-right [] [] [] = refl
drift-join-distrib-right (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (∧-dist-∨ʳ x y z)
             (drift-join-distrib-right xs ys zs)
