{-# OPTIONS --safe --without-K #-}

{- ═══════════════════════════════════════════════════════════════════════════════

   MASS FROM TOPOLOGY
   ══════════════════
   
   Why mass ratios emerge from K₄ graph invariants
   
   STATUS: EXPLORATION — Not yet proven, testing hypotheses
   
   ═══════════════════════════════════════════════════════════════════════════════
   
   THESIS
   ══════
   
   Mass is NOT a free parameter. It emerges from:
   
   1. TOPOLOGICAL STRUCTURE: K₄ has fixed invariants (V=4, E=6, χ=2, deg=3)
   2. MEMORY SATURATION: The system cannot hold more than V distinctions
   3. WINDING MODES: Particles are topological defects with winding numbers
   
   The key insight: When D₃ emerges from memory saturation (§7 in FirstDistinction),
   the number of WAYS to wind around the structure determines mass.
   
   ═══════════════════════════════════════════════════════════════════════════════
   
   THE ARGUMENT
   ════════════
   
   Phase 0: D₀ exists (the First Distinction)
            This creates Bool = {⊤, ⊥}
   
   Phase 1: Self-reference creates D₁, D₂
            Each distinction must distinguish itself from others
   
   Phase 2: Memory saturates at D₃
            Cannot hold more than 4 distinctions in mutual reference
            → K₄ emerges as the UNIQUE stable structure (proven in §7.3)
   
   Phase 3: Winding modes appear
            Once K₄ exists, there are WAYS to traverse it
            These ways are counted by powers of deg = 3
   
   Phase 4: Mass = Winding complexity
            More complex windings = higher mass
            Simplest winding (electron) = reference mass m_e
   
   ═══════════════════════════════════════════════════════════════════════════════ -}

module MassFromTopology where

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 1  BASIC DEFINITIONS (self-contained)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Natural numbers
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Addition
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- Multiplication
_×_ : ℕ → ℕ → ℕ
zero × _ = zero
suc m × n = n + (m × n)

-- Exponentiation
_^_ : ℕ → ℕ → ℕ
_ ^ zero = 1
b ^ suc e = b × (b ^ e)

infixl 6 _+_
infixl 7 _×_
infixr 8 _^_

-- Propositional equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 2  K₄ INVARIANTS (from FirstDistinction §7-8)
-- ═══════════════════════════════════════════════════════════════════════════════

-- These are DERIVED in FirstDistinction.agda, not postulated
-- K₄ = complete graph on 4 vertices

V : ℕ        -- Vertices (distinctions)
V = 4

E : ℕ        -- Edges (mutual relations)  
E = 6        -- = V(V-1)/2 = 4×3/2

χ : ℕ        -- Euler characteristic
χ = 2        -- = V - E + F = 4 - 6 + 4 (tetrahedron)

deg : ℕ      -- Degree (connections per vertex)
deg = 3      -- = V - 1 (complete graph)


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 3  DERIVED QUANTITIES
-- ═══════════════════════════════════════════════════════════════════════════════

-- Spinor modes: 2^V
-- WHY: Each vertex can be in state ⊤ or ⊥ (from D₀ = Bool)
-- This gives Clifford algebra dimension 2^4 = 16

spinor-modes : ℕ
spinor-modes = 2 ^ V

spinor-modes-is-16 : spinor-modes ≡ 16
spinor-modes-is-16 = refl


-- Sector count: 2^V + 1 = 17
-- WHY: 16 spinor modes + 1 scalar mode (the "vacuum")
-- This is the "Fermat prime" F₂ = 2^(2²) + 1

F₂ : ℕ
F₂ = spinor-modes + 1

F₂-is-17 : F₂ ≡ 17
F₂-is-17 = refl


-- Winding volume: deg³ = 27
-- WHY: A path can wind around 3 independent cycles
-- Each cycle has 3 choices (the 3 edges from any vertex)

winding-volume : ℕ
winding-volume = deg ^ deg

winding-volume-is-27 : winding-volume ≡ 27
winding-volume-is-27 = refl


-- Spin factor: χ² = 4
-- WHY: Euler characteristic counts topological charge
-- Squared because particles have spin-1/2 (need 2 rotations)

spin-factor : ℕ
spin-factor = χ ^ χ

spin-factor-is-4 : spin-factor ≡ 4
spin-factor-is-4 = refl


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 4  THE MASS FORMULA STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   HYPOTHESIS: Mass ratios have the form
   
     m / m_e = (spin modes) × (winding volume) × (sector structure)
   
   For bound states of n constituents with winding dimension d:
   
     m / m_e = χⁿ × deg^d × f(V)
   
   where f(V) depends on whether it's:
   - Lepton: fermionic, uses F₂ = 2^V + 1
   - Hadron: bound state, uses winding sums
   - Boson: gauge field, uses eigenvalue λ = V
-}


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 5  PROTON: THE PARADIGM CASE
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   Proton = 3 quarks bound by color
   
   Structure:
   - 3 constituents → need χ² spin factor (spin-1/2 → spin-1/2)  
   - 3 independent windings → deg³ winding volume
   - Fermionic → F₂ sector structure
   
   Prediction: m_p / m_e = χ² × deg³ × F₂
                        = 4 × 27 × 17
                        = 1836
   
   Experiment: 1836.153
   Error: 0.008%
-}

proton-mass-ratio : ℕ
proton-mass-ratio = spin-factor × winding-volume × F₂

proton-prediction : proton-mass-ratio ≡ 1836
proton-prediction = refl


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 6  WHY THESE FACTORS?
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   χ² = 4 (SPIN FACTOR)
   ═══════════════════
   
   The Euler characteristic χ = 2 counts "handles" on a surface.
   For K₄ skeleton (tetrahedron), χ = V - E + F = 4 - 6 + 4 = 2.
   
   A spin-1/2 particle needs 720° rotation to return to initial state.
   This is captured by χ² = 4, the "double cover" factor.
   
   Mathematically: SU(2) is double cover of SO(3)
   From K₄: The 4 vertices form a representation of the quaternion group
   

   deg³ = 27 (WINDING VOLUME)
   ══════════════════════════
   
   Each vertex of K₄ has degree 3 (connected to all others).
   A path starting at any vertex has 3 choices at each step.
   
   For a bound state of 3 constituents (quarks):
   - Each quark can wind in 3 directions
   - Total winding configurations: 3 × 3 × 3 = 27
   
   This is the "phase space" of the bound state.
   

   F₂ = 17 (SECTOR STRUCTURE)  
   ══════════════════════════
   
   The 16 spinor modes (2^V) plus vacuum gives 17 sectors.
   
   For fermions, 17 is special: it's the Fermat prime F₂ = 2^4 + 1.
   Fermat primes are exactly divisible into a circle (Gauss).
   
   This means: fermion sectors tile the rotation group perfectly.
   The proton's 17 factor comes from this perfect tiling.
-}


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 7  CONSISTENCY CHECK: α⁻¹ = 137
-- ═══════════════════════════════════════════════════════════════════════════════

-- The fine structure constant emerges from K₄ in FirstDistinction §18c
-- α⁻¹ = spinor-modes × κ + 1 + E + χ
--     = 16 × 8 + 1 + 6 + 2
--     = 128 + 9
--     = 137

κ : ℕ
κ = 8  -- Derived in §18 as deg² - 1 = 9 - 1 = 8

α-inverse : ℕ
α-inverse = spinor-modes × κ + 1 + E + χ

α-inverse-is-137 : α-inverse ≡ 137
α-inverse-is-137 = refl

-- The same K₄ invariants that give α also give proton mass
-- This is NOT coincidence - it's the same topology!


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 8  SUMMARY: WHY MASS FROM TOPOLOGY
-- ═══════════════════════════════════════════════════════════════════════════════

{-
   The argument in one paragraph:
   
   When the First Distinction D₀ creates Bool = {⊤, ⊥}, it forces the emergence
   of D₁, D₂, D₃ through self-reference (each must be distinguished from others).
   Memory saturation at 4 distinctions yields K₄ as the UNIQUE stable structure.
   
   K₄ has fixed invariants: V=4, E=6, χ=2, deg=3.
   These invariants determine ALL possible "ways to be different" in the system.
   
   A particle is a PATTERN of distinctions - a way of winding through K₄.
   The complexity of the winding (how many factors of deg, χ, V) determines mass.
   
   The electron is the SIMPLEST fermion: m_e = 1 (reference).
   The proton is a 3-quark bound state: m_p/m_e = χ² × deg³ × F₂ = 1836.
   
   This is not numerology. The factors have geometric meaning:
   - χ² = spin structure (double cover)
   - deg³ = winding volume (3-constituent bound state)  
   - F₂ = sector structure (fermion mode count)
   
   The same topology that gives d=3 spatial dimensions also gives mass ratios.
   It MUST - there's only one K₄.
   
   ═══════════════════════════════════════════════════════════════════════════════
   
   NEXT: BoundStates.agda — Why 3-quark states have deg³ factor
         WaveModes.agda  — Why fermions have F₂ = 17 sectors
   
   ═══════════════════════════════════════════════════════════════════════════════ -}
