{-# OPTIONS --safe #-}

----------------------------------------------------------------------
--  Step 12 ▸ Rank-3 Soundness
--  * Gegenrichtung zu Step 11: rank3? xs ≡ true  ⇒  HasGoodTriple xs
--  * plus: Slice-Variante auf DriftGraph (über Step 10/11)
----------------------------------------------------------------------

module Structures.Step12_Rank3_Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool      using (Bool; true; false; if_then_else_; not)
open import Data.Nat       using (ℕ; zero; suc)
open import Data.List      using (List; []; _∷_; map)

-- Wir benutzen die Definitionen aus Step 11 (ℤ³, det3, diffs, Checker/Spec)
open import Structures.Step11_Rank3 using
  ( ℤ ; ℤ³ ; mk3
  ; nonZeroℤ
  ; det3
  ; diffs
  ; GoodTriple ; HasGoodTriple ; here ; there
  ; rank3? ; rank3Witness
  ; toZ3
  )

-- Für die Slice-Variante (History & numerische Punkte)
open import Structures.Step7_DriftGraph  using (DriftGraph)
open import Structures.Step10_FoldMap    using (Embed3NatAt ; historyAt)

----------------------------------------------------------------------
-- 0) Hilfslemma: isJust-Charakterisierung (lokal)
--    (nur für Bequemlichkeit; wir entfalten rank3? direkt)
----------------------------------------------------------------------

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

isJust : ∀ {a} {A : Set a} → Maybe A → Bool
isJust nothing  = false
isJust (just _) = true

----------------------------------------------------------------------
-- 1) Soundness auf Listenebene
--    Idee: Entfalte rank3? / rank3Witness auf dem Kopf-Triple.
--          Falls det ≠ 0: "here". Falls det = 0: reduziere auf Tail und nutze Induktion.
----------------------------------------------------------------------

soundness : ∀ (xs : List ℤ³) → rank3? xs ≡ true → HasGoodTriple xs
-- Längen < 3: unmöglich, da rank3? = false per Definition
soundness []            pr = let impossible : false ≡ true
                                 impossible = pr       -- rank3? [] = false
                             in  case impossible of λ ()
soundness (_ ∷ [])      pr = let impossible = pr       -- ebenso
                             in  case impossible of λ ()
soundness (_ ∷ _ ∷ [])  pr = let impossible = pr
                             in  case impossible of λ ()

-- Hauptfall: mindestens drei Punkte
soundness (u ∷ v ∷ w ∷ rs) pr with nonZeroℤ (det3 u v w)
... | true  = here refl
... | false =
  -- In diesem Zweig expandiert rank3Witness per Definition auf die Tail-Liste.
  -- Also reduziert sich rank3? (u∷v∷w∷rs) ≡ rank3? (v∷w∷rs).
  -- Aus pr folgern wir Induktionsvoraussetzung auf (v∷w∷rs), und heben mit 'there' wieder an.
  let pr' : rank3? (v ∷ w ∷ rs) ≡ true
      pr' = pr
  in there (soundness (v ∷ w ∷ rs) pr')

----------------------------------------------------------------------
-- 2) Slice-Soundness: Checker auf dem Zeit-Slice ⇒ existierender Zeuge
--    Wir bleiben bewusst "listen-nah": konstruieren die ℤ³-Punkte wie in Step 11
--    und wenden soundness auf deren Differenzen an.
----------------------------------------------------------------------

soundnessOnSlice :
  (G : DriftGraph) (t : ℕ) →
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  rank3? (diffs ptsZ) ≡ true → HasGoodTriple (diffs ptsZ)
soundnessOnSlice G t pr =
  let ptsZ = map toZ3 (Embed3NatAt G t)
  in  soundness (diffs ptsZ) pr
