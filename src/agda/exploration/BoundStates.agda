{-# OPTIONS --safe --without-K #-}

{- ═══════════════════════════════════════════════════════════════════════════════

   BOUND STATES
   ════════════
   
   Why n-constituent bound states have deg^n winding factor
   
   STATUS: EXPLORATION — Developing the theory
   
   ═══════════════════════════════════════════════════════════════════════════════
   
   THESIS
   ══════
   
   A bound state of n constituents has mass factor deg^n because:
   
   1. Each constituent can wind independently around K₄
   2. K₄ has degree = 3 (each vertex connects to 3 others)
   3. Total winding configurations = 3^n
   
   This explains:
   - Proton (3 quarks): deg³ = 27
   - Pion (quark-antiquark): deg² = 9  
   - Electron (no substructure): deg⁰ = 1
   
   ═══════════════════════════════════════════════════════════════════════════════ -}

module BoundStates where

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 1  BASIC DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════════

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_×_ : ℕ → ℕ → ℕ
zero × _ = zero
suc m × n = n + (m × n)

_^_ : ℕ → ℕ → ℕ
_ ^ zero = 1
b ^ suc e = b × (b ^ e)

infixl 6 _+_
infixl 7 _×_
infixr 8 _^_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 2  K₄ INVARIANTS
-- ═══════════════════════════════════════════════════════════════════════════════

V : ℕ
V = 4

deg : ℕ
deg = 3        -- V - 1 for complete graph

χ : ℕ
χ = 2          -- Euler characteristic

F₂ : ℕ
F₂ = 17        -- 2^V + 1


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 3  THE WINDING PRINCIPLE
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   WHY deg^n FOR n CONSTITUENTS?
   ═════════════════════════════
   
   Consider a random walk on K₄ starting at any vertex:
   
   Step 0: At vertex A
   Step 1: Can go to B, C, or D (3 choices = deg)
   Step 2: From new vertex, 3 more choices
   ...
   
   For n independent constituents:
   - Constituent 1 has deg choices
   - Constituent 2 has deg choices  
   - Constituent n has deg choices
   - Total: deg^n configurations
   
   This is the "winding phase space" of the bound state.
   
   
   ANALOGY: KNOT THEORY
   ════════════════════
   
   In knot theory, complexity is measured by crossing number.
   More crossings = more complex knot = "higher mass".
   
   Similarly, more constituents = more winding possibilities = higher mass.
   
   The K₄ graph is like the "space" in which the knot lives.
   deg = 3 is the local branching factor.
-}


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 4  BOUND STATE MASS FORMULA
-- ═══════════════════════════════════════════════════════════════════════════════

-- Winding factor for n constituents
winding-factor : ℕ → ℕ
winding-factor n = deg ^ n

-- Examples
winding-1 : winding-factor 1 ≡ 3
winding-1 = refl

winding-2 : winding-factor 2 ≡ 9
winding-2 = refl

winding-3 : winding-factor 3 ≡ 27
winding-3 = refl


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 5  PARTICLE CLASSIFICATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   ELEMENTARY PARTICLES (n = 0)
   ════════════════════════════
   
   No internal winding → deg⁰ = 1
   Mass comes from other factors (spin, sector)
   
   Examples:
   - Electron: elementary lepton
   - Photon: elementary boson
   
   
   MESONS (n = 2)  
   ═══════════════
   
   Quark-antiquark pair → deg² = 9
   
   Examples:
   - Pion (π): m ≈ 273 m_e
     Prediction: deg² × (something) = 9 × 30 ≈ 270
   
   - Kaon (K): m ≈ 966 m_e
     Prediction: deg² × (something else)
   
   
   BARYONS (n = 3)
   ════════════════
   
   Three quarks → deg³ = 27
   
   Examples:
   - Proton: m_p/m_e = χ² × deg³ × F₂ = 4 × 27 × 17 = 1836 ✓
   - Neutron: m_n/m_e ≈ 1839 (slightly heavier, electromagnetic correction)
-}


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 6  THE PROTON IN DETAIL
-- ═══════════════════════════════════════════════════════════════════════════════

-- Proton = 3 quarks
proton-constituents : ℕ
proton-constituents = 3

-- Winding factor
proton-winding : ℕ
proton-winding = winding-factor proton-constituents

proton-winding-is-27 : proton-winding ≡ 27
proton-winding-is-27 = refl

-- Spin factor (from χ)
spin-factor : ℕ
spin-factor = χ × χ

spin-factor-is-4 : spin-factor ≡ 4
spin-factor-is-4 = refl

-- Full proton mass
proton-mass-ratio : ℕ
proton-mass-ratio = spin-factor × proton-winding × F₂

proton-is-1836 : proton-mass-ratio ≡ 1836
proton-is-1836 = refl


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 7  WHY 3 QUARKS?
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   WHY ARE BARYONS MADE OF 3 QUARKS?
   ═════════════════════════════════
   
   From K₄: deg = 3 (each vertex has 3 neighbors)
   
   A "color-neutral" bound state needs:
   - Equal contribution from all "directions"
   - 3 directions in K₄ (the 3 edges from any vertex)
   - Therefore: 3 constituents, one per direction
   
   This is why:
   - Quarks have 3 colors (red, green, blue)
   - Baryons need 3 quarks (one of each color)
   - Color confinement = can't have free color
   
   The number 3 is NOT arbitrary:
   - It's deg = V - 1 = 4 - 1 = 3
   - Determined by K₄ being the minimal stable graph
   
   
   ANALOGY: TRAFFIC INTERSECTION
   ══════════════════════════════
   
   At a 4-way intersection, each road connects to 3 others.
   A "balanced flow" requires traffic from all 3 directions.
   
   K₄ is the simplest structure with this property.
   Quarks are like traffic, baryons are like balanced intersections.
-}


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 8  COLOR AS K₄ DIRECTION
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   HYPOTHESIS: Color charge = edge direction in K₄
   
   From any vertex A in K₄:
   - Edge to B = "red"
   - Edge to C = "green"  
   - Edge to D = "blue"
   
   A quark "at A going to B" has color red.
   An antiquark "at B going to A" has color anti-red.
   
   A color-neutral state needs:
   - 3 quarks: A→B, A→C, A→D (all directions covered)
   OR
   - Quark-antiquark: A→B and B→A (direction and reverse)
   
   This is exactly how QCD color charge works!
   
   
   SU(3) FROM K₄
   ═════════════
   
   The symmetry group of K₄ edge directions is S₃ (permutations).
   S₃ embeds in SU(3) as the Weyl group.
   
   Full SU(3) emerges when we include:
   - Edge directions (discrete S₃)
   - Phase rotations (continuous U(1) at each vertex)
   
   This gives: S₃ × U(1)³ → SU(3) after gauge fixing
-}

-- Number of colors = degree of K₄
colors : ℕ
colors = deg

colors-is-3 : colors ≡ 3
colors-is-3 = refl


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 9  MESON MASS FORMULA
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   Mesons have 2 constituents (quark + antiquark)
   Winding factor: deg² = 9
   
   But mesons are lighter than baryons - why?
   
   ANSWER: Different sector structure
   
   Baryons (3 quarks): fermionic → F₂ = 17
   Mesons (qq̄ pair): bosonic → different factor
   
   For pion (lightest meson):
   - m_π/m_e ≈ 273
   - Prediction: deg² × χ × F₂ - adjustment?
   
   This needs more work - see WaveModes.agda for boson vs fermion sectors.
-}

meson-winding : ℕ
meson-winding = deg × deg

meson-winding-is-9 : meson-winding ≡ 9
meson-winding-is-9 = refl


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 10  SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   KEY RESULTS
   ═══════════
   
   1. Bound states have winding factor deg^n for n constituents
   2. deg = 3 from K₄ topology (each vertex has 3 neighbors)
   3. This explains why baryons have 3 quarks (color neutrality)
   4. Proton: n=3 → deg³=27 → m_p/m_e = 4×27×17 = 1836
   
   
   WHAT'S MISSING
   ══════════════
   
   - Full derivation of meson masses (need boson sector theory)
   - Why χ² instead of χ (spin-statistics connection)
   - Excited states (higher winding modes)
   
   
   NEXT: WaveModes.agda — Fermion vs boson sector structures
   
   ═══════════════════════════════════════════════════════════════════════════════ -}
