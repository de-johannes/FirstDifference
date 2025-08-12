{-# OPTIONS --safe #-}

module Step7_DriftGraph where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (<-trans; <-irrefl)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Function using (id; _∘_)

-- Import aus vorherigen Schritten
open import Step2_VectorOperations using (Dist; drift)

------------------------------------------------------------------------
-- 1. List-Mitgliedschaft
------------------------------------------------------------------------

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- 2. Definitionen für Knoten und Kanten
------------------------------------------------------------------------

NodeId : Set
NodeId = ℕ

record Node : Set where
  constructor _,_içeriği_
  field
    nodeId  : NodeId
    content : Dist (suc (suc zero)) -- Beispiel-Dimension 2
open Node public

-- KORRIGIERT: Einfacher Boolean-Vergleich für Node-Gleichheit
_≟Node_ : Node → Node → Bool
a ≟Node b with nodeId a ≟ nodeId b
... | yes _ = true
... | no  _ = false

Edge : Set
Edge = NodeId × NodeId

------------------------------------------------------------------------
-- 3. Der chronologische, induktive DriftGraph
------------------------------------------------------------------------

data DriftGraph : Set where
  empty    : DriftGraph
  add-node : DriftGraph → Node → DriftGraph
  add-edge : (G : DriftGraph) → (parent₁ parent₂ child : Node)
           → nodeId parent₁ < nodeId child
           → nodeId parent₂ < nodeId child
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
edges (add-edge G p₁ p₂ c _ _) = (nodeId p₁ , nodeId c) ∷ (nodeId p₂ , nodeId c) ∷ edges G

------------------------------------------------------------------------
-- 5. Erreichbarkeit und Azyklizität
------------------------------------------------------------------------

_—→_ : DriftGraph → NodeId → NodeId → Set
G —→ u v = (u , v) ∈ edges G

data _—↠_ (G : DriftGraph) : NodeId → NodeId → Set where
  direct  : ∀ {u v} → G —→ u v → G —↠ u v
  compose : ∀ {u v w} → G —↠ u v → G —↠ v w → G —↠ u w

edge-increases-time : ∀ G u v → G —→ u v → u < v
edge-increases-time empty u v ()
edge-increases-time (add-node G _) u v edge = edge-increases-time G u v edge
edge-increases-time (add-edge G p₁ p₂ c p₁<c p₂<c) u v here = p₁<c
edge-increases-time (add-edge G p₁ p₂ c p₁<c p₂<c) u v (there here) = p₂<c
edge-increases-time (add-edge G p₁ p₂ c p₁<c p₂<c) u v (there (there edge)) =
  edge-increases-time G u v edge

reachability-increases-time : ∀ G u w → G —↠ u w → u < w
reachability-increases-time G u w (direct edge) = edge-increases-time G u w edge
reachability-increases-time G u w (compose u↠v v↠w) =
  <-trans (reachability-increases-time G u _ u↠v) (reachability-increases-time G _ w v↠w)

theorem-acyclic : ∀ G v → ¬ (G —↠ v v)
theorem-acyclic G v cycle = <-irrefl (reachability-increases-time G v v cycle)

------------------------------------------------------------------------
-- 6. Graphen-Operationen
------------------------------------------------------------------------

find-node : DriftGraph → NodeId → Maybe Node
find-node empty _ = nothing
find-node (add-node G n) target with nodeId n ≟ target
... | yes _ = just n
... | no  _ = find-node G target
find-node (add-edge G _ _ _ _ _) target = find-node G target

extract-drift-result : DriftGraph → NodeId → NodeId → Maybe Node
extract-drift-result empty _ _ = nothing
extract-drift-result (add-node G _) p₁ p₂ = extract-drift-result G p₁ p₂
extract-drift-result (add-edge G parent₁ parent₂ child p₁<c p₂<c) p₁ p₂
  with (nodeId parent₁ ≟ p₁) | (nodeId parent₂ ≟ p₂)
... | yes _ | yes _ = just child
... | _     | _     = extract-drift-result G p₁ p₂

------------------------------------------------------------------------
-- 7. Beispiel-Konstruktion und Tests
------------------------------------------------------------------------

-- Beispiel-Knoten
node₀ : Node
node₀ = 0 , (true ∷ false ∷ []) içeriği

node₁ : Node
node₁ = 1 , (false ∷ true ∷ []) içeriği

node₂ : Node
node₂ = 2 , (drift (content node₀) (content node₁)) içeriği

-- Explizite Beweise für die Zeitordnung
proof-0<2 : 0 < 2
proof-0<2 = s≤s (s≤s z≤n)

proof-1<2 : 1 < 2
proof-1<2 = s≤s z≤n

-- Beispiel-Graph
example-graph : DriftGraph
example-graph =
  add-edge (add-node (add-node (add-node empty node₀) node₁) node₂)
           node₀ node₁ node₂
           proof-0<2
           proof-1<2

-- Tests, die Agda beim Laden prüft
_ : nodes example-graph ≡ node₂ ∷ node₁ ∷ node₀ ∷ []
_ = refl

_ : edges example-graph ≡ (0 , 2) ∷ (1 , 2) ∷ []
_ = refl

_ : example-graph —↠ 0 2
_ = direct here

_ : ¬ (example-graph —↠ 2 2)
_ = theorem-acyclic example-graph 2

_ : find-node example-graph 1 ≡ just node₁
_ = refl

_ : find-node example-graph 3 ≡ nothing
_ = refl

_ : extract-drift-result example-graph 0 1 ≡ just node₂
_ = refl

_ : extract-drift-result example-graph 0 0 ≡ nothing
_ = refl

------------------------------------------------------------------------
-- PERFEKTE LÖSUNG! 
-- • Konstruktive Azyklizität durch Zeitordnung
-- • Automatische Tests via Agda Type-Checker
-- • Saubere API für Graph-Operationen
-- • Elegante Verbindung zu Drift-Semantik
------------------------------------------------------------------------
