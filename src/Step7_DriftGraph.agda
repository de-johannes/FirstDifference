{-# OPTIONS --safe #-}

module Step7_DriftGraph where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (<-trans)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
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
  constructor node[_içeriği_]
  field
    nodeId  : NodeId
    content : Dist (suc (suc zero)) -- Beispiel-Dimension 2
open Node public

_≟NodeId_ : Node → NodeId → Bool
a ≟NodeId id with nodeId a ≟ id
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

_—→_within_ : NodeId → NodeId → DriftGraph → Set
u —→ v within G = (u , v) ∈ edges G
infix 4 _—→_within_

data _can-reach_within_ (u w : NodeId) : DriftGraph → Set where
  direct  : ∀ {G} → u —→ w within G → u can-reach w within G
  compose : ∀ {G v} → u can-reach v within G → v can-reach w within G → u can-reach w within G
infix 4 _can-reach_within_

edge-increases-time : ∀ u v G → u —→ v within G → u < v
edge-increases-time u v empty ()
edge-increases-time u v (add-node G n) edge = edge-increases-time u v G edge
edge-increases-time u v (add-edge G p₁ p₂ c p₁<c p₂<c) here = p₁<c
edge-increases-time u v (add-edge G p₁ p₂ c p₁<c p₂<c) (there here) = p₂<c
edge-increases-time u v (add-edge G p₁ p₂ c p₁<c p₂<c) (there (there edge)) =
  edge-increases-time u v G edge

reachability-increases-time : ∀ u w G → u can-reach w within G → u < w
reachability-increases-time u w G (direct edge) = edge-increases-time u w G edge
reachability-increases-time u w G (compose u↠v v↠w) =
  <-trans (reachability-increases-time u _ G u↠v) (reachability-increases-time _ w G v↠w)

-- Hilfsfunktion: Zeigt, dass suc v ≤ v unmöglich ist
suc≤v→⊥ : ∀ v → suc v ≤ v → ⊥
suc≤v→⊥ zero ()
suc≤v→⊥ (suc v) (s≤s p) = suc≤v→⊥ v p

theorem-acyclic : ∀ G v → ¬ (v can-reach v within G)
theorem-acyclic G v cycle = suc≤v→⊥ v (reachability-increases-time v v G cycle)

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
extract-drift-result (add-edge G parent₁ parent₂ child _ _) p₁ p₂
  with (parent₁ ≟NodeId p₁) ∧ (parent₂ ≟NodeId p₂)
... | true  = just child
... | false with (parent₁ ≟NodeId p₂) ∧ (parent₂ ≟NodeId p₁)
...   | true  = just child
...   | false = extract-drift-result G p₁ p₂

------------------------------------------------------------------------
-- 7. Beispiel-Konstruktion und Tests
------------------------------------------------------------------------

node₀ : Node
node₀ = node[ 0 içeriği (true ∷ false ∷ []) ]

node₁ : Node
node₁ = node[ 1 içeriği (false ∷ true ∷ []) ]

node₂ : Node
node₂ = node[ 2 içeriği (drift (content node₀) (content node₁)) ]

-- KORRIGIERTE BEWEISE für m < n (definiert als suc m ≤ n)
proof-0<2 : 0 < 2
proof-0<2 = s≤s z≤n

proof-1<2 : 1 < 2
proof-1<2 = s≤s (s≤s z≤n)

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

_ : 0 —→ 2 within example-graph
_ = here

_ : 0 can-reach 2 within example-graph
_ = direct here

_ : ¬ (2 can-reach 2 within example-graph)
_ = theorem-acyclic example-graph 2

_ : find-node example-graph 1 ≡ just node₁
_ = refl

_ : extract-drift-result example-graph 0 1 ≡ just node₂
_ = refl
