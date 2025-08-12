module Structures.Functors where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-suc)
open import Data.Unit using (⊤; tt)

-- CutCat: wir qualifizieren alles mit C und vermeiden _≤_-Kollisionen
open import Structures.CutCat as C using (refl≤; z≤n; s≤s) renaming (_≤_ to _≤ᴄ_; _∙_ to _∙ᴄ_)
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg
  ; plus; plus-hom; shiftHom; shift-id
  ; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg     public

------------------------------------------------------------------------
-- Difference from a ≤-witness: returns n − m, and diff (refl≤ m) ≡ 0 def.
------------------------------------------------------------------------

diff : ∀ {m n} → m _≤ᴄ_ n → ℕ
diff {zero}   {n}     z≤n      = n
diff {suc m}  {suc n} (s≤s p)  = diff {m} {n} p

-- Helper: “walking” the witness adds exactly its length
end-eq : ∀ {b c} (g : b _≤ᴄ_ c) → b + diff g ≡ c
end-eq {zero}   {c}     z≤n     = +-identityˡ c
end-eq {suc b}  {suc c} (s≤s g) =
  -- suc b + diff (s≤s g)  ≡  suc (b + diff g)  ≡  suc c
  cong suc (trans (+-suc b (diff g)) (end-eq g))

-- Composition law for diff
diff-∙ : ∀ {a b c} (f : a _≤ᴄ_ b) (g : b _≤ᴄ_ c) → diff (f C._∙ᴄ_ g) ≡ diff f + diff g
diff-∙ {zero}   {b} {c}  z≤n      g =            -- z≤n ∙ g = z≤n  (type-general)
  -- diff (z≤n ∙ g) = c  and  diff z≤n + diff g = b + diff g = c
  trans refl (sym (end-eq g))
diff-∙ {suc a} {suc b} {suc c} (s≤s f) (s≤s g) =
  -- diff (s≤s f ∙ s≤s g) = diff (f ∙ g)  ≡  diff f + diff g
  diff-∙ f g

------------------------------------------------------------------------
-- Functor CutCat → DistOpAlg  (Semantic Time)
------------------------------------------------------------------------

F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m _≤ᴄ_ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

-- object mapping (for explicit reference)
semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality
------------------------------------------------------------------------

-- Identity: diff (refl≤ m) reduces to 0, hence shift-id applies pointwise
F-id : ∀ {m} n → (F-arr (C.refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id n = shift-id n

-- Composition: (_∘Alg_ (F-arr g) (F-arr f)).f n = plus (diff g) (plus (diff f) n)
--             = (n + diff f) + diff g  ≡⟨+-assoc⟩ n + (diff f + diff g)
--             = plus (diff f + diff g) n  ≡⟨sym (diff-∙ f g)⟩  plus (diff (f ∙ᴄ g)) n
F-comp :
  ∀ {a b c} (f : a _≤ᴄ_ b) (g : b _≤ᴄ_ c) (n : ℕ) →
    (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (f C._∙ᴄ_ g)) .f n
F-comp f g n
  rewrite +-assoc n (diff f) (diff g)
        | sym (diff-∙ f g) = refl
