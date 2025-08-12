module Structures.Functors where

-- This module formalises "semantic time" T(n) from Part I of the Backbone PDF.
-- Semantic time counts irreducible drift events and maps them to ℕ via the initial
-- algebra (NAlg, suc) as a functor: CutCat ⟶ DistOpAlg.

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-assoc)
open import Data.Unit using (⊤; tt)

-- Import our custom category and operad structures
import Structures.CutCat as CC
import Structures.DistOpOperad as DO

------------------------------------------------------------------------
-- Arithmetic definition: difference (n - m) from a ≤-witness
------------------------------------------------------------------------

diff : ∀ {m n} → m CC._≤_ n → ℕ
diff {m} {n} p = go m n p
  where
    go : ∀ m n → m CC._≤_ n → ℕ
    go zero     n       CC.z≤n     = n
    go (suc m') (suc n') (CC.s≤s p') = go m' n' p'

-- Lemma: diff refl≤ m = 0
diff-refl : ∀ m → diff (CC.refl≤ m) ≡ 0
diff-refl zero    = refl
diff-refl (suc m) = diff-refl m

-- Lemma: diff composition = sum of diffs
diff-comp : ∀ {a b c} (f : a CC._≤_ b) (g : b CC._≤_ c) →
              diff (f CC.∙ g) ≡ diff f + diff g
diff-comp CC.z≤n      _            = refl
diff-comp (CC.s≤s f) (CC.s≤s g) =
  cong suc (diff-comp f g)

------------------------------------------------------------------------
-- Functor CutCat → DistOpAlg  (Semantic Time)
------------------------------------------------------------------------

F-obj : ℕ → DO.DistOpAlg lzero
F-obj _ = DO.NAlg

F-arr : ∀ {m n} → m CC._≤_ n → DO.HomAlg (F-obj m) (F-obj n)
F-arr p = DO.shiftHom (diff p)

-- Semantic time as object mapping only (for explicit reference)
semanticTime : ℕ → DO.Carrier DO.NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality proofs
------------------------------------------------------------------------

-- Identity: diff (refl≤ m) = 0, so shiftHom 0 = idAlg
F-id : ∀ {m} n → (F-arr (CC.refl≤ m)) .DO.f n ≡ (DO.idAlg (F-obj m)) .DO.f n
F-id {m} n = trans (cong (λ k → DO.plus k n) (diff-refl m)) (DO.shift-id n)

-- Composition: diff (f ∙ g) = diff f + diff g, so shifts compose additively
F-comp :
  ∀ {a b c} (f : a CC._≤_ b) (g : b CC._≤_ c) n →
    (DO._∘Alg_ (F-arr g) (F-arr f)) .DO.f n ≡ (F-arr (f CC.∙ g)) .DO.f n
F-comp f g n =
  cong (λ k → DO.plus k n) (diff-comp f g)
