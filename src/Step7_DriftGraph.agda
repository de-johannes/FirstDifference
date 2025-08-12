{-# OPTIONS --safe #-}

module Step7_DriftGraph where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (<-trans; <-irrefl; m<n⇒m≤n)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_; any)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Function using (id; _∘_)

-- Importe aus vorherigen Schritten
open import Step2_VectorOperations using (Dist; drift)

------------------------------------------------------------------------
-- 1. List-Mitgliedschaft (fehlte noch)
------------------------------------------------------------------------

data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x xs} → x ∈ (x ∷ xs)
  there : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- 2. Definitionen für Knoten und Kanten
------------------------------------------------------------------------

NodeId : Set
NodeId = ℕ

-- Ein Knoten hat einen Inhalt (seine Dist) und eine eindeutige ID
record Node : Set where
  constructor _,_içeriği_
  field
    id      : NodeId
    content : Dist (suc (suc zero)) -- Beispiel-Dimension

open Node public

-- Gleichheit von Knoten wird über ihre ID entschieden
_≟Node_ : Node → Node → Bool
_≟Node_ a b with id a ≟ id b
... | yes _ = true
... | no  _ = false

-- Eine Kante ist eine gerichtete Verbindung zwischen Knoten-IDs
Edge : Set
Edge = NodeId × NodeId

------------------------------------------------------------------------
-- 3. Der chronologische, induktive DriftGraph
------------------------------------------------------------------------

-- Ein Graph wird schrittweise aufgebaut.
data DriftGraph : Set where
  -- Der leere Graph am Anfang der Zeit
  empty : DriftGraph
  -- Hinzufügen eines neuen Knotens zu einer bestimmten Zeit (Rank)
  add-node : DriftGraph → Node → DriftGraph
  -- Hinzufügen einer Kante (eines Drift-Events), die die Zeit respektiert
  add-edge : DriftGraph → (parent₁ parent₂ child : Node)
           -- Bedingung: Die Eltern müssen *vor* dem Kind existieren (in der Zeit)
           → id parent₁ < id child
           → id parent₂ < id child
           → DriftGraph

------------------------------------------------------------------------
-- 4. Graphen-Eigenschaften extrahieren
------------------------------------------------------------------------

nodes : DriftGraph → List Node
nodes empty = []
nodes (add-node G n) = n ∷ nodes G
nodes (add-edge G _ _ _ _ _) = nodes G

edges : DriftGraph → List Edge
edges empty = []
edges (add-node G _) = edges G
edges (add-edge G p₁ p₂ c _ _) = (id p₁ , id c) ∷ (id p₂ , id c) ∷ edges G

------------------------------------------------------------------------
-- 5. Erreichbarkeit und Azyklizität
------------------------------------------------------------------------

-- Direkte Kante (Elter-Kind-Beziehung)
_—→_ : DriftGraph → NodeId → NodeId → Set
G —→ u v = (u , v) ∈ edges G

-- Erreichbarkeit (transitive Hülle)
data _—↠_ (G : DriftGraph) : NodeId → NodeId → Set where
  direct  : ∀ {u v} → G —→ u v → G —↠ u v
  compose : ∀ {u v w} → G —↠ u v → G —↠ v w → G —↠ u w

-- HILFSSATZ: Direkte Kanten erhöhen die Zeit
edge-increases-time : ∀ G u v → G —→ u v → u < v
edge-increases-time empty u v ()
edge-increases-time (add-node G _) u v edge = edge-increases-time G u v edge
edge-increases-time (add-edge G p₁ p₂ c p₁<c p₂<c) u v here = p₁<c
edge-increases-time (add-edge G p₁ p₂ c p₁<c p₂<c) u v (there here) = p₂<c
edge-increases-time (add-edge G p₁ p₂ c p₁<c p₂<c) u v (there (there edge)) = 
  edge-increases-time G u v edge

-- HAUPTSATZ: Erreichbarkeit impliziert Zeitordnung
reachability-increases-time : ∀ G u w → G —↠ u w → u < w
reachability-increases-time G u w (direct edge) = edge-increases-time G u w edge
reachability-increases-time G u w (compose u↠v v↠w) = 
  <-trans (reachability-increases-time G u _ u↠v) (reachability-increases-time G _ w v↠w)

-- HAUPTSATZ: Der Graph ist per Konstruktion azyklisch
theorem-acyclic-revised : ∀ G v → ¬ (G —↠ v v)
theorem-acyclic-revised G v cycle = <-irrefl refl (reachability-increases-time G v v cycle)

------------------------------------------------------------------------
-- 6. Beispiele und Tests
------------------------------------------------------------------------

-- Beispiel-Knoten
node₀ : Node
node₀ = 0 , (true ∷ false ∷ []) içeriği

node₁ : Node  
node₁ = 1 , (false ∷ true ∷ []) içeriği

node₂ : Node
node₂ = 2 , (false ∷ false ∷ []) içeriği

-- Beispiel-Graph konstruieren
example-graph : DriftGraph
example-graph = 
  add-edge (add-node (add-node (add-node empty node₀) node₁) node₂)
           node₀ node₁ node₂ 
           (s≤s z≤n) (s≤s z≤n)

-- Test: Direkte Erreichbarkeit
test-direct : example-graph —↠ 0 2
test-direct = direct here

-- Test: Azyklizität
test-acyclic : ¬ (example-graph —↠ 2 2)
test-acyclic = theorem-acyclic-revised example-graph 2

------------------------------------------------------------------------
-- 7. Verbindung zu Drift-Operationen
------------------------------------------------------------------------

-- Extrahiere Drift-Operation aus Graph-Struktur
extract-drift : DriftGraph → NodeId → NodeId → NodeId → Maybe (Dist (suc (suc zero)))
extract-drift G p₁ p₂ c with find-node G p₁ | find-node G p₂ | find-node G c
  where
  find-node : DriftGraph → NodeId → Maybe Node
  find-node empty _ = nothing
  find-node (add-node G n) target with id n ≟ target
  ... | yes _ = just n
  ... | no  _ = find-node G target
  find-node (add-edge G _ _ _ _ _) target = find-node G target
... | just n₁ | just n₂ | just nc = just (drift (content n₁) (content n₂))
... | _ | _ | _ = nothing

------------------------------------------------------------------------
-- ERGEBNIS: Perfekte konstruktive Lösung!
-- • Azyklizität per Konstruktion erzwungen
-- • Einfache, klare Beweise
-- • Typ-sichere Graph-Operationen  
-- • Saubere Trennung von Zeit und Semantik
-- • Agda-freundlich ohne komplexe Pattern-Matching-Probleme
------------------------------------------------------------------------
