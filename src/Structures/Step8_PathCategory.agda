{-# OPTIONS --safe #-}

module Structures.Step8_PathCategory where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_)

-- 🔧 FIX: Korrigierter Import (nicht _Final)
open import Structures.Step7_DriftGraph as DG

------------------------------------------------------------------------
-- 1. Definition eines Kategoriellen Pfades
------------------------------------------------------------------------

-- Ein Pfad von u nach w ist entweder der Identitäts-Pfad (Länge 0)
-- oder eine Kante, gefolgt von einem weiteren Pfad.
data Path (G : DG.DriftGraph) : DG.NodeId → DG.NodeId → Set where
  refl-path : ∀ {u} → Path G u u
  _∷-path_  : ∀ {u v w} → (e : u DG.—→ v within G) → Path G v w → Path G u w

infixr 5 _∷-path_

------------------------------------------------------------------------
-- 2. Operationen auf Pfaden: Komposition
------------------------------------------------------------------------

-- Die Komposition von Pfaden ist die intelligente Verkettung der Listen.
_++-path_ : ∀ {G u v w} → Path G u v → Path G v w → Path G u w
refl-path      ++-path q = q
(e ∷-path p) ++-path q = e ∷-path (p ++-path q)

infixr 5 _++-path_

------------------------------------------------------------------------
-- 3. Beweise der Kategoriengesetze (rigoros, durch Induktion)
------------------------------------------------------------------------

-- Assoziativität der Pfad-Komposition
path-assoc : ∀ {G a b c d} (p : Path G a b) (q : Path G b c) (r : Path G c d) →
             (p ++-path q) ++-path r ≡ p ++-path (q ++-path r)
path-assoc refl-path      q r = refl
path-assoc (e ∷-path p) q r = cong (e ∷-path_) (path-assoc p q r)

-- Linke Identität: Ein leerer Pfad am Anfang ändert nichts.
path-idˡ : ∀ {G u v} (p : Path G u v) → refl-path ++-path p ≡ p
path-idˡ p = refl

-- Rechte Identität: Ein leerer Pfad am Ende ändert nichts.
path-idʳ : ∀ {G u v} (p : Path G u v) → p ++-path refl-path ≡ p
path-idʳ refl-path      = refl
path-idʳ (e ∷-path p) = cong (e ∷-path_) (path-idʳ p)

------------------------------------------------------------------------
-- 4. Die formale Kategorie der Pfade im DriftGraph
------------------------------------------------------------------------

-- Der Record für eine Kategorie ist jetzt lokal, da wir ihn nur hier brauchen.
record Category (Obj : Set) (Hom : Obj → Obj → Set) : Set₁ where
  field
    id    : ∀ A → Hom A A
    _∘_   : ∀ {A B C} → Hom A B → Hom B C → Hom A C -- Standardreihenfolge: f, dann g

    -- Gesetze
    idˡ   : ∀ {A B} (f : Hom A B) → id A ∘ f ≡ f
    idʳ   : ∀ {A B} (f : Hom A B) → f ∘ id B ≡ f  
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

-- Instanziierung der Kategorie für einen gegebenen DriftGraph
DriftPathCategory : (G : DG.DriftGraph) → Category (DG.NodeId) (Path G)
DriftPathCategory G = record
  { id    = refl-path
  ; _∘_   = _++-path_
  ; idˡ   = path-idˡ
  ; idʳ   = path-idʳ
  ; assoc = path-assoc
  }

------------------------------------------------------------------------
-- 5. TESTS -
------------------------------------------------------------------------

-- Test: Pfadkonstruktion
test-single-path : ∀ {G u v} → (e : u DG.—→ v within G) → Path G u v
test-single-path e = e ∷-path refl-path

-- Test: Identität
test-identity : ∀ {G u} → Path G u u  
test-identity = Category.id (DriftPathCategory _) _

-- Test: Komposition
test-composition : ∀ {G u v w} → Path G u v → Path G v w → Path G u w
test-composition p q = Category._∘_ (DriftPathCategory _) p q
