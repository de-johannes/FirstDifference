{-# OPTIONS --safe #-}

module Step8_PathCategory where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_)

-- Wir importieren deinen verifizierten Graphen als Grundlage.
open import Structures.Step7_DriftGraph_Final as DG

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
-- KORRIGIERT: {G} als implizites Argument hinzugefügt.
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
-- KORRIGIERT: {G} als implizites Argument hinzugefügt.
path-idˡ : ∀ {G u v} (p : Path G u v) → refl-path ++-path p ≡ p
path-idˡ p = refl

-- Rechte Identität: Ein leerer Pfad am Ende ändert nichts.
-- KORRIGIERT: {G} als implizites Argument hinzugefügt.
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
    idˡ   : ∀ {A B} (f : Hom A B) → id ∘ f ≡ f
    idʳ   : ∀ {A B} (f : Hom A B) → f ∘ id ≡ f
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
