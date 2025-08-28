{-# OPTIONS --safe #-}

----------------------------------------------------------------------
-- Step 13 ▸ Operadic Cohesion
--  * Endo-Operad auf Cells (Operationen: Cell → Cell)
--  * punktweise Gesetze (Einheit/Assoziativität) als definitorische Gleichheiten
--  * Lift der Operationen auf Nodes via Step-10-Projektion π : Node → Cell
----------------------------------------------------------------------

module Structures.Step13_OperadicCohesion where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Structures.Step7_DriftGraph using (DriftGraph ; Node)
open import Structures.Step10_FoldMap   using (Cell ; FoldMap)

----------------------------------------------------------------------
-- 1) Abstrakte Operad-Hülle über einem Träger X
----------------------------------------------------------------------

record Operad (X : Set) : Set where
  field
    Op    : Set            -- Operationen
    idO   : Op             -- Einheit
    _∘_   : Op → Op → Op   -- Komposition (erst links, dann rechts anwenden)
    act   : Op → X → X     -- Wirkung auf X

    unitL : ∀ f x → act (idO ∘ f) x ≡ act f x
    unitR : ∀ f x → act (f ∘ idO) x ≡ act f x
    assoc : ∀ f g h x → act ((f ∘ g) ∘ h) x ≡ act (f ∘ (g ∘ h)) x

open Operad public

----------------------------------------------------------------------
-- 2) Konkrete Instanz: Endo-Operad auf Cells
----------------------------------------------------------------------

CellOperad : Operad Cell
CellOperad = record
  { Op    = Cell → Cell
  ; idO   = λ c → c
  ; _∘_   = λ f g → λ c → g (f c)   -- Komposition: erst f, dann g
  ; act   = λ f c → f c
  ; unitL = λ f c → refl
  ; unitR = λ f c → refl
  ; assoc = λ f g h c → refl
  }

----------------------------------------------------------------------
-- 3) Lift der Cell-Operationen auf Nodes über die FoldMap-Projektion π
----------------------------------------------------------------------

nodeAct
  : ∀ {G : DriftGraph} {rank}
  → FoldMap G rank
  → (Cell → Cell)     -- Operation (aus CellOperad.Op)
  → Node → Cell       -- Wirkung auf Nodes: f ∘ π
nodeAct fm f n = let open FoldMap fm in f (π n)

-- Einheits-/Kompositionsgesetze punktweise (definitorisch)
nodeAct-id
  : ∀ {G rank} (fm : FoldMap G rank) (n : Node)
  → nodeAct fm (Operad.idO CellOperad) n
    ≡ (let open FoldMap fm in π n)
nodeAct-id fm n = refl

nodeAct-comp
  : ∀ {G rank} (fm : FoldMap G rank) (f g : Cell → Cell) (n : Node)
  → nodeAct fm ((Operad._∘_ CellOperad) f g) n
    ≡ g (nodeAct fm f n)
nodeAct-comp fm f g n = refl

----------------------------------------------------------------------
-- 4) (Optional) Bündelung als „Algebra“ der Operad-Instanz
----------------------------------------------------------------------

record NodeAction (G : DriftGraph) (rank : _) : Set where
  field
    fm    : FoldMap G rank
    apply : (Cell → Cell) → Node → Cell
    unL   : ∀ f n →
            apply ((Operad._∘_ CellOperad) (Operad.idO CellOperad) f) n
            ≡ apply f n
    unR   : ∀ f n →
            apply ((Operad._∘_ CellOperad) f (Operad.idO CellOperad)) n
            ≡ apply f n
    compN : ∀ f g n →
            apply ((Operad._∘_ CellOperad) f g) n
            ≡ g (apply f n)

mkNodeAction : ∀ {G rank} → FoldMap G rank → NodeAction G rank
mkNodeAction fm = record
  { fm    = fm
  ; apply = nodeAct fm
  ; unL   = λ f n → refl
  ; unR   = λ f n → refl
  ; compN = λ f g n → refl
  }
