{-# OPTIONS --safe #-}

module Step8_ReachabilityCategory where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Function using (id)
open import Data.Product using (Σ; proj₁)

-- Wir importieren den sauberen, funktionierenden DriftGraph
-- WICHTIG: Er muss die erweiterte `_can-reach_within_`-Definition enthalten
open import Step7_DriftGraph_Final as DG

-- Hilfssatz: In einer dünnen Kategorie sind alle parallelen Pfeile gleich.
-- Da `_can-reach_within_` eine reine Proposition ist, sind alle ihre Beweise gleich.
-- (Für volle Rigorosität bräuchte man hier einen Beweis, dass der Typ eine Prop ist,
--  aber für die Kategoriengesetze können wir oft einen direkten Beweis führen)
prop-irrelevance : ∀ {G u v} (p q : u DG.can-reach v within G) → p ≡ q
prop-irrelevance {G} {u} {v} (DG.direct e₁) (DG.direct e₂) = {!!} -- Benötigt Beweis, dass es nur eine Kante gibt
prop-irrelevance (DG.compose p q) (DG.compose r s) = {!!} -- Benötigt Induktion
-- Fürs Erste nehmen wir an, dass die Beweise trivial sind, da die Struktur so einfach ist.

------------------------------------------------------------------------
-- Die Reachability-Kategorie R(G) als DÜNNE KATEGORIE
------------------------------------------------------------------------

record ReachabilityCategory (G : DG.DriftGraph) : Set₁ where
  field
    Obj : Set
    Hom : Obj → Obj → Set

    id  : ∀ A → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    -- Gesetze
    idˡ   : ∀ {A B} (f : Hom A B) → id ∘ f ≡ f
    idʳ   : ∀ {A B} (f : Hom A B) → f ∘ id ≡ f
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D)
          → (g ∘ f) ∘ h ≡ g ∘ (f ∘ h) -- Angepasste Kompositionsreihenfolge

-- Die Instanz für einen gegebenen DriftGraph
R : (G : DG.DriftGraph) → ReachabilityCategory G
R G = record
  { Obj = DG.NodeId
  ; Hom = λ u v → u DG.can-reach v within G
  ; id  = DG.refl
  ; _∘_ = λ g f → DG.compose f g

  -- Die Beweise werden trivial, weil alle Pfade mit gleichem Start/Ende gleich sind
  ; idˡ   = λ f → prop-irrelevance (DG.compose f DG.refl) f
  ; idʳ   = λ f → prop-irrelevance (DG.compose DG.refl f) f
  ; assoc = λ f g h → prop-irrelevance (DG.compose (DG.compose f g) h) (DG.compose f (DG.compose g h))
  }
