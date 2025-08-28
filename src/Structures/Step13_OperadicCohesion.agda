{-# OPTIONS --safe #-}

module Structures.Step13_OperadicCohesion where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Structures.Step7_DriftGraph using (DriftGraph ; Node)
open import Structures.Step10_FoldMap   using (Cell ; FoldMap)

------------------------------------------------------------------------
-- 1) Universe-polymorphe Operade
------------------------------------------------------------------------

record Operad (ℓX ℓO : Level) (X : Set ℓX) : Set (lsuc (ℓX ⊔ ℓO)) where
  field
    Op    : Set ℓO
    idO   : Op
    _∘_   : Op → Op → Op
    act   : Op → X → X

    unitL : ∀ f x → act (idO ∘ f) x ≡ act f x
    unitR : ∀ f x → act (f ∘ idO) x ≡ act f x
    assoc : ∀ f g h x → act ((f ∘ g) ∘ h) x ≡ act (f ∘ (g ∘ h)) x

open Operad public

------------------------------------------------------------------------
-- 2) Endo-Operad auf Cells (gleicher Level für Träger & Ops)
------------------------------------------------------------------------

CellOperad : Operad lzero lzero Cell
CellOperad = record
  { Op    = Cell → Cell
  ; idO   = λ c → c
  ; _∘_   = λ f g → λ c → g (f c)       -- erst f, dann g
  ; act   = λ f c → f c
  ; unitL = λ f c → refl
  ; unitR = λ f c → refl
  ; assoc = λ f g h c → refl
  }

------------------------------------------------------------------------
-- 3) Lift der Cell-Operationen auf Nodes via π aus FoldMap
------------------------------------------------------------------------

nodeAct
  : ∀ {G : DriftGraph} {rank}
  → FoldMap G rank
  → (Cell → Cell)
  → Node → Cell
nodeAct fm f n = let open FoldMap fm in f (π n)

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

------------------------------------------------------------------------
-- 4) Bündelung als NodeAction-„Algebra“
------------------------------------------------------------------------

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
