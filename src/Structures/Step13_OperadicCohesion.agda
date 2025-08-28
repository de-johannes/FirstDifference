{-# OPTIONS --safe #-}

----------------------------------------------------------------------
-- Step 13 ▸ Operadic Cohesion
--  * Endo-Operad auf Cells (Operationen: Cell → Cell)
--  * punktweise Gesetze (Einheit/Assoziativität) als definitorische Gleichheiten
--  * Lift der Operationen auf Nodes via Step-10-Projektion π : Node → Cell
----------------------------------------------------------------------

module Structures.Step13_OperadicCohesion where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Primitive using (Level)
open import Data.Unit using (⊤; tt)

open import Structures.Step7_DriftGraph using (DriftGraph ; Node)
open import Structures.Step10_FoldMap   using
  ( Cell ; FoldMap ; buildFold )

----------------------------------------------------------------------
-- 1) Abstrakte Operad-Hülle über einem Träger X
----------------------------------------------------------------------

record Operad (X : Set) : Set where
  field
    Op    : Set            -- Operationen
    idO   : Op             -- Einheit
    _∘_   : Op → Op → Op   -- Komposition (erst links, dann rechts anwenden)
    act   : Op → X → X     -- wie Operationen auf X wirken

    unitL : ∀ (f : Op) (x : X) → act (idO ∘ f) x ≡ act f x
    unitR : ∀ (f : Op) (x : X) → act (f ∘ idO) x ≡ act f x
    assoc : ∀ (f g h : Op) (x : X)
          → act ((f ∘ g) ∘ h) x ≡ act (f ∘ (g ∘ h)) x

open Operad public

----------------------------------------------------------------------
-- 2) Konkrete Instanz: Endo-Operad auf Cells
----------------------------------------------------------------------

CellOperad : Operad Cell
CellOperad = record
  { Op    = Cell → Cell
  ; idO   = (λ c → c)
  ; _∘_   = (λ f g → λ c → g (f c))   -- Komposition: erst f, dann g
  ; act   = (λ f c → f c)
  ; unitL = λ f c → refl
  ; unitR = λ f c → refl
  ; assoc = λ f g h c → refl
  }

----------------------------------------------------------------------
-- 3) Lift der Cell-Operationen auf Nodes über die FoldMap-Projektion π
--    Fixiere ein G und einen Rank; benutze π aus (buildFold G rank).
----------------------------------------------------------------------

-- Für ein gegebenes FoldMap-Objekt definieren wir die Wirkung auf Nodes:
nodeAct
  : ∀ {G : DriftGraph} {rank : _}
  → FoldMap G rank
  → (Cell → Cell)                 -- Operation (aus CellOperad.Op)
  → Node → Cell                   -- Wirkung auf Nodes: f ∘ π
nodeAct fm f n = f (FoldMap.π fm n)

-- Punktweise Einheiten-/Kompositionsgesetze für die Node-Wirkung
nodeAct-id
  : ∀ {G rank} (fm : FoldMap G rank) (n : Node)
  → nodeAct fm (Operad.idO CellOperad) n ≡ FoldMap.π fm n
nodeAct-id fm n = refl

nodeAct-comp
  : ∀ {G rank} (fm : FoldMap G rank) (f g : Cell → Cell) (n : Node)
  → nodeAct fm ((Operad._∘_ CellOperad) f g) n
    ≡ g (nodeAct fm f n)
nodeAct-comp fm f g n = refl

----------------------------------------------------------------------
-- 4) (Optionale) Bündelung: Node-Action als Algebra über der Operad-Instanz
--    – keine zusätzlichen Beweise nötig, da alle Gesetze punktweise 'refl' sind.
----------------------------------------------------------------------

record NodeAction (G : DriftGraph) (rank : _) : Set where
  field
    fm    : FoldMap G rank
    apply : (Cell → Cell) → Node → Cell
    unL   : ∀ (f : Cell → Cell) (n : Node)
          → apply ((Operad._∘_ CellOperad) (Operad.idO CellOperad) f) n
            ≡ apply f n
    unR   : ∀ (f : Cell → Cell) (n : Node)
          → apply ((Operad._∘_ CellOperad) f (Operad.idO CellOperad)) n
            ≡ apply f n
    compN : ∀ (f g : Cell → Cell) (n : Node)
          → apply ((Operad._∘_ CellOperad) f g) n
            ≡ (apply g n)                       -- g(f(π n)) punktweise

mkNodeAction : ∀ {G rank} → FoldMap G rank → NodeAction G rank
mkNodeAction fm = record
  { fm    = fm
  ; apply = nodeAct fm
  ; unL   = λ f n → refl
  ; unR   = λ f n → refl
  ; compN = λ f g n → refl
  }
