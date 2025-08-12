module Structures.Functors where

open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)

-- Wichtig: alias, damit wir C._≤_, C.refl≤, C.s≤s, C._∙_ benutzen
open import Structures.CutCat as C using (_∙_; refl≤; s≤s) renaming (_≤_ to _≤ᴄ_)
open import Structures.DistOpOperad using
  ( DistOpAlg; HomAlg; NAlg
  ; plus; plus-hom; shiftHom; shift-id
  ; idAlg; _∘Alg_ )

open DistOpAlg public
open HomAlg public

------------------------------------------------------------------------
-- difference: zählt die s≤s-Schritte im CutCat-≤-Zeugen
------------------------------------------------------------------------

diff : ∀ {m n} → m _≤ᴄ_ n → ℕ
diff (C.refl≤ _) = 0
diff (C.s≤s p)   = suc (diff p)

------------------------------------------------------------------------
-- Functor CutCat → DistOpAlg  (Semantic Time)
------------------------------------------------------------------------

F-obj : ℕ → DistOpAlg lzero
F-obj _ = NAlg

F-arr : ∀ {m n} → m _≤ᴄ_ n → HomAlg (F-obj m) (F-obj n)
F-arr p = shiftHom (diff p)

semanticTime : ℕ → Carrier NAlg
semanticTime n = n

------------------------------------------------------------------------
-- Functoriality
------------------------------------------------------------------------

-- Identity: diff (refl≤ m) ≡ 0 definitorisch ⇒ shift-id passt
F-id : ∀ {m} n → (F-arr (C.refl≤ m)) .f n ≡ (idAlg (F-obj m)) .f n
F-id n = shift-id n

-- Composition (reduziert, falls _∘Alg_ Shifts additiv komponiert)
F-comp :
  ∀ {a b c} (g : b _≤ᴄ_ c) (f : a _≤ᴄ_ b) n →
    (_∘Alg_ (F-arr g) (F-arr f)) .f n ≡ (F-arr (g C._∙_ f)) .f n
F-comp g f n = refl
