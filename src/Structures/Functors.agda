module Structures.Functors where

-- === Imports ===
open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-suc)

-- Wir importieren unsere eigenen Module qualifiziert, um Namenskonflikte zu vermeiden.
open import Structures.CutCat as Cat
open import Structures.DistOpOperad as Alg

-- Wir öffnen die Records, um auf die Felder zugreifen zu können.
open Cat.Category Cat.CutCat public
open Alg.DistOpAlg public
open Alg.HomAlg public

------------------------------------------------------------------------
-- 1. Eine Funktion, die aus einem Zeitpfeil (m ≤ n) die Dauer (n - m) extrahiert.
------------------------------------------------------------------------

duration : ∀ {m n} → Hom m n → ℕ
duration {zero}  {n}   Cat.z≤n      = n
duration {suc m} {suc n} (Cat.s≤s p) = duration p

-- Beweis: Startzeit + Dauer = Endzeit
end-point-proof : ∀ {m n} (p : Hom m n) → m + duration p ≡ n
end-point-proof {zero}  {n}   Cat.z≤n      = +-identityˡ n
end-point-proof {suc m} {suc n} (Cat.s≤s p) =
  -- suc m + duration p  ≡ suc (m + duration p) ≡ suc n
  trans (cong suc (+-suc m (duration p))) (cong suc (end-point-proof p))

-- Beweis: Die Dauer von komponierten Pfeilen ist die Summe der Dauern.
duration-comp : ∀ {a b c} (f : Hom a b) (g : Hom b c) → duration (f Cat.∘ g) ≡ duration f + duration g
duration-comp {zero}  {b} {c} Cat.z≤n      g = trans refl (sym (end-point-proof g))
duration-comp {suc a} {suc b} {suc c} (Cat.s≤s f) (Cat.s≤s g) = duration-comp f g

------------------------------------------------------------------------
-- 2. Definition des Funktors F: CutCat → DistOpAlg
--    Ein Funktor bildet Objekte auf Objekte und Pfeile auf Pfeile (Morphismen) ab.
------------------------------------------------------------------------

-- F bildet jedes Objekt (eine Zahl n) auf dasselbe Objekt ab: (ℕ, succ).
F-obj : Obj → Alg.DistOpAlg lzero
F-obj _ = Alg.NAlg

-- F bildet jeden Pfeil (einen Beweis m ≤ n) auf einen Algebra-Morphismus ab.
-- Dieser Morphismus ist die Funktion "addiere die Dauer des Pfeils".
F-hom : ∀ {m n} → Hom m n → Alg.HomAlg (F-obj m) (F-obj n)
F-hom p .f    = Alg.plus (duration p)
F-hom p .hom  = Alg.plus-hom (duration p)

------------------------------------------------------------------------
-- 3. Beweis der Funktorialität
--    Ein Funktor muss Identität und Komposition erhalten.
------------------------------------------------------------------------

-- Beweis 1: F erhält Identitätspfeile.
-- F(id m) muss der Identitätsmorphismus auf F(m) sein.
-- F(id m) ist "plus (duration (refl≤ m))", was "plus 0" ist.
-- Wir müssen zeigen, dass (n + 0) ≡ n ist.
F-preserves-id : ∀ {m} → F-hom (Cat.id m) ≡ Alg.idAlg (F-obj m)
F-preserves-id {m} =
  -- Wir müssen die Gleichheit von Records beweisen, also die Gleichheit aller Felder.
  -- Hier gibt es nur 'f' und 'hom'. 'hom' ist trivial durch refl.
  -- Für 'f' müssen wir beweisen: (λ n → Alg.plus (duration (Cat.id m)) n) ≡ (λ n → n)
  -- Das reduziert sich zu: (λ n → n + 0) ≡ (λ n → n), was durch Alg.shift-id bewiesen wird.
  record { f = Alg.shift-id; hom = refl }

-- Beweis 2: F erhält Komposition.
-- F(f ∘ g) muss F(f) ∘ F(g) sein.
-- F(f ∘ g) ist "plus (duration (f ∘ g))".
-- F(f) ∘ F(g) ist "plus (duration g) ∘ plus (duration f)", was "plus (duration f + duration g)" ist.
-- Der Kern des Beweises ist unser Lemma "duration-comp".
F-preserves-comp : ∀ {a b c} (f : Hom a b) (g : Hom b c) → F-hom (f Cat.∘ g) ≡ (F-hom f Alg.∘Alg F-hom g)
F-preserves-comp {a} {b} {c} f g =
  record
    { f   = trans (cong Alg.plus (duration-comp f g)) (+-assoc _ _ _)
    ; hom = refl
    }
