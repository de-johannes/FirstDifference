module Structures.Functors where

-- === Imports ===
open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-suc)

-- Wir importieren unsere eigenen Module, ohne sie sofort zu öffnen.
import Structures.CutCat as C
import Structures.DistOpOperad as A

-- Erst jetzt öffnen wir die spezifische Kategorie-Instanz, mit der wir arbeiten.
-- Das bringt C.Obj, C.Hom, C.id und C. _∘_ in den Namespace.
open C.Category C.CutCat

------------------------------------------------------------------------
-- 1. Eine Funktion, die aus einem Zeitpfeil (m ≤ n) die Dauer (n - m) extrahiert.
------------------------------------------------------------------------

duration : ∀ {m n} → Hom m n → ℕ
duration {zero}  {n}   C.z≤n      = n
duration {suc m} {suc n} (C.s≤s p) = duration p

-- Beweis: Startzeit + Dauer = Endzeit
end-point-proof : ∀ {m n} (p : Hom m n) → m + duration p ≡ n
end-point-proof {zero}  {n}   C.z≤n      = +-identityˡ n
end-point-proof {suc m} {suc n} (C.s≤s p) =
  trans (cong suc (+-suc m (duration p))) (cong suc (end-point-proof p))

-- Beweis: Die Dauer von komponierten Pfeilen ist die Summe der Dauern.
duration-comp : ∀ {a b c} (f : Hom a b) (g : Hom b c) → duration (f C.∘ g) ≡ duration f + duration g
duration-comp {zero}  {b} {c} C.z≤n      g = trans refl (sym (end-point-proof g))
duration-comp {suc a} {suc b} {suc c} (C.s≤s f) (C.s≤s g) = duration-comp f g

------------------------------------------------------------------------
-- 2. Definition des Funktors F: CutCat → DistOpAlg
------------------------------------------------------------------------

-- F bildet jedes Objekt (eine Zahl n) auf die initiale Algebra (ℕ, succ).
F-obj : Obj → A.DistOpAlg lzero
F-obj _ = A.NAlg

-- F bildet jeden Pfeil (m ≤ n) auf einen Algebra-Morphismus ab
-- (die Funktion "addiere die Dauer des Pfeils").
F-hom : ∀ {m n} → Hom m n → A.HomAlg (F-obj m) (F-obj n)
F-hom p .A.f    = A.plus (duration p)
F-hom p .A.hom  = A.plus-hom (duration p)

------------------------------------------------------------------------
-- 3. Beweis der Funktorialität
------------------------------------------------------------------------

-- Beweis 1: F erhält Identitätspfeile. F(id m) ≡ id_{F(m)}
-- F(id m) ist "plus (duration (refl≤ m))", was "plus 0" ist.
F-preserves-id : ∀ {m} → F-hom (C.id m) ≡ A.idAlg (F-obj m)
F-preserves-id {m} =
  -- Um die Gleichheit von Records zu beweisen, beweisen wir die Gleichheit der Felder.
  A.record
    { A.f   = A.shift-id
    ; A.hom = refl
    }

-- Beweis 2: F erhält Komposition. F(f ∘ g) ≡ F(f) ∘ F(g)
F-preserves-comp : ∀ {a b c} (f : Hom a b) (g : Hom b c) → F-hom (f C.∘ g) ≡ (F-hom f A.∘Alg F-hom g)
F-preserves-comp {a} {b} {c} f g =
  A.record
    { A.f   = trans (cong (A.plus) (duration-comp f g)) (+-assoc _ _ _)
    ; A.hom = refl
    }
