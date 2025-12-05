---
layout: default
title: Predictions
---

# Predictions

All values computed from K₄ structure alone. No free parameters.

**Epistemological note:** The mathematical computations below are **proven** in Agda. That these mathematical results correspond to physical constants is a **hypothesis** supported by numerical agreement.

---

## Structural Results (Proven)

These follow mathematically from K₄ structure:

| Quantity | Formula | K₄ Result | Matches Physics? |
|----------|---------|-----------|------------------|
| Spatial dimensions | λ=4 multiplicity | **d = 3** | ✓ (3 observed) |
| Fermion generations | λ=4 multiplicity | **3** | ? (hypothesis) |
| Time dimensions | drift irreversibility | **1** | ✓ (1 observed) |
| Metric signature | symmetric vs. asymmetric | **(−,+,+,+)** | ✓ (GR signature) |
| **Speed of light** | **max propagation = 1 edge/tick** | **c = 1** | ✓ (necessary) |
| Spin states | \|Bool\| = 2 | **2** | ? (numerical match) |
| Gyromagnetic ratio | g = \|Bool\| | **g = 2** | ? (numerical match) |
| Spinor components | \|Bool\|² | **4** | ? (numerical match) |
| γ-matrices | \|V\| = 4 | **4** | ? (numerical match) |
| Clifford dimension | 2^V | **16** | ✓ (math fact) |
| Λ sign | λ₁ > 0 | **Λ > 0** | ✓ (accelerating expansion) |
| Ricci scalar | Tr(L) | **R = 12** | (discrete, no direct comparison) |
| Coupling constant | dim×χ = 4×2 | **κ = 8** | ✓ (8πG → 8 in Planck units) |

### Why c = 1 is Necessary (Not Just Convenient)

On a discrete graph, the speed of information propagation is constrained:

| Option | Meaning | Consistent? |
|--------|---------|-------------|
| c = 0 | Nothing propagates | ❌ No dynamics |
| c = 1 | One edge per tick | ✅ **Only option** |
| c > 1 | Skip edges | ❌ Violates locality |
| c = ∞ | Instantaneous | ❌ Violates causality |

**c = 1 is not a choice — it's the unique value compatible with graph structure.**

The number "299,792,458 m/s" is pure unit conversion: c = 1 ℓ_P/t_P in natural units.

---

## Numerical Coincidences?

These K₄ formulas produce values remarkably close to measured physical constants.

### Fine Structure Constant α

The K₄ spectral formula computes a number:

#### Operad Derivation

The 8 coherence laws of the operad have specific arities:

| Algebraic Laws | Arity | Categorical Laws | Arity |
|----------------|-------|------------------|-------|
| 1. Associativity | 3 | 5. Involutivity | 2 |
| 2. Distributivity | 3 | 6. Cancellativity | 4 |
| 3. Neutrality | 2 | 7. Irreducibility | 2 |
| 4. Idempotence | 1 | 8. Confluence | 4 |
| **SUM** | **9 = deg²** | **PRODUCT** | **64 = λ³** |

The formula emerges as:

$$\alpha^{-1} = \Pi(\text{categorical arities}) \times \chi + \Sigma(\text{algebraic arities})$$

$$= (2 \times 4 \times 2 \times 4) \times 2 + (3+3+2+1) = 64 \times 2 + 9 = 137$$

**Why SUM vs PRODUCT?** (from Drift/CoDrift signatures)
- **Δ : D×D → D** (convergent, 2→1) → inputs ADD → **Sum**
- **∇ : D → D×D** (divergent, 1→2) → outputs MULTIPLY → **Product**
- χ = 2 = Drift-CoDrift duality (doubles the modes)

This is the Σ vs Π duality from type theory, computed from the First Distinction.

**Bonus:** κ = 8 = number of operad laws!

[→ Full Operad explanation](operad)

#### Spectral Form

$$\alpha^{-1} = \lambda^3 \chi + \deg^2 + \frac{V}{\deg(E^2 + 1)}$$

Where ALL parameters are K₄ spectral/topological invariants:
- λ = 4 (spectral gap of Laplacian)
- χ = 2 (Euler characteristic)
- deg = 3 (vertex degree)
- V = 4 (vertices)
- E = 6 (edges)

**Calculation:**
- λ³χ = 4³ × 2 = 128 (spectral-topological term)
- deg² = 3² = 9 (vertex connectivity squared)
- V/(deg(E²+1)) = 4/111 = 0.036... (higher-order correction)

| | Value |
|---|-------|
| **K₄ formula** | 137.036036... |
| **CODATA 2018** | 137.035999084(21) |
| **Agreement** | 0.000027% |

**Interpretation:** The K₄ formula computes 137.036. The physical α⁻¹ is 137.036. This is either a profound connection or a remarkable coincidence. The mathematical computation is proven; the physical identification is hypothesis.

*The spectral gap λ=4 emerges from the K₄ Laplacian eigenvalues {0,4,4,4}. The exponent 3 in λ³ equals d (the spatial dimension), making this a discrete analog of the QED phase-space integral ∫d³k. This is the same λ that determines d=3 via its multiplicity.*

### Cosmic Age τ

The formula for N is structurally derived from K₄:

$$N = 5 \times 4^{100}$$

**Full structural derivation:**

$$N = (\text{spacetime} + \text{observer}) \times (\text{states})^{\text{capacity}}$$
$$N = ((d+1) + 1) \times V^{E^2 + \kappa^2} = 5 \times 4^{100}$$

| Component | Value | Derivation | Status |
|-----------|-------|------------|--------|
| **5** | (d+1)+1 | spacetime dimensions + observer | ✅ 5 equivalent proofs |
| **4** | V = λ | K₄ vertices = spectral gap | ✅ Theorem |
| **100** | E²+κ² | information capacity (Pythagorean) | ✅ K₄ unique! |

**Why 5?** Five equivalent derivations:
- (d+1)+1 = 4+1 = 5 (spacetime + observer)
- V+1 = 4+1 = 5 (vertices + centroid)
- E−1 = 6−1 = 5 (edges − self-reference)
- κ−d = 8−3 = 5 (coupling − dimension)
- λ+1 = 4+1 = 5 (spectral gap + 1)

**Why 100?** K₄ is the ONLY complete graph where E²+κ² is a perfect square:
- K₃: 3²+6² = 45 ✗
- K₄: 6²+8² = 100 = 10² ✓
- K₅: 10²+10² = 200 ✗

**Physical mechanism:** E and κ are orthogonal information channels (topological vs. dynamical). Pythagoras: capacity = E² + κ² = 100. Universe branches into V=4 states per epoch until saturation.

$$\tau = N \times t_{\text{Planck}} = 13.726 \text{ Gyr}$$

| | Value |
|---|-------|
| **K₄ formula** | 13.726 Gyr |
| **Planck 2018** | 13.787 ± 0.020 Gyr |
| **SH0ES (Cepheids)** | 12.6 ± 0.4 Gyr |
| **Agreement (Planck)** | 0.44% (3.0σ) |

**Interpretation:** The K₄ formula produces an epoch count that, when multiplied by Planck time, gives 13.73 Gyr. Whether this is the actual cosmic age is hypothesis, but the 0.44% agreement is notable.

---

### Wilson Loop / Confinement

The Wilson loop expectation values emerge analytically from K₄:

$$W(n) = \exp\left(-\frac{s}{s_{\max}}\right)$$

where s = λ + E + χ/V = 4 + 6 + 0.5 = **10.5** measures total information flow.

#### Derivation

| Component | Value | Meaning |
|-----------|-------|---------|
| λ = 4 | spectral | wave propagation rate |
| E = 6 | connectivity | direct neighbor access |
| χ/V = 0.5 | topology | curvature per vertex |
| **s = 10.5** | **total** | information capacity |

For specific loop sizes:
- **W(3)** = exp(−1/deg²) = exp(−1/9) ≈ **0.895 ≈ 91%**
- **W(6)** = exp(−s/s_max) = exp(−1) = 1/e ≈ **0.368 ≈ 37%**

The scaling relation: W(6) = W(3)^(s) = (0.895)^10.5 ≈ 0.37

**Physical interpretation:** Larger loops probe deeper into the K₄ structure. The 10.5 combines three orthogonal information modes — spectral (how waves spread), topological (connectivity), and geometric (curvature). *(This is more speculative than the α and τ formulas.)*

---

### Cosmological Constant Λ

A proposed explanation for the "10⁻¹²² problem":

$$\Lambda_{\text{obs}} = \frac{\Lambda_{\text{bare}}}{N^2} = \frac{3}{N^2}$$

With N ~ 10⁶¹ Planck times elapsed:

$$\Lambda_{\text{obs}}/\Lambda_{\text{Planck}} \sim 10^{-122}$$

**Status:** This is a **hypothesis** about the Λ ratio, not a proven computation like α. The mechanism (dilution) is plausible but not formalized.

---

## Classification

| Category | Meaning | Examples |
|----------|---------|----------|
| **Computed** | Machine-verified formula in Agda | K₄ structure, formulas |
| **Matches** | Numerical agreement with observation | α, τ, d=3 |
| **Hypothesis** | Identification with physics | "137.036 IS α⁻¹" |

### What is COMPUTED (Agda --safe --without-K):
- **d = 3** from eigenvector multiplicity of K₄ Laplacian
- **Signature (−,+,+,+)** from drift irreversibility
- **χ = 2** computed as V − E + F = 4 − 6 + 4
- **κ = 8** from dim × χ = 4 × 2
- **λ = 4** as Laplacian eigenvalue (L·φ = 4·φ)
- **Formula result: 137.036** from λ³χ + deg² + V/(deg(E²+1))
- **N = 5 × 4¹⁰⁰** from structural derivation

### What is HYPOTHESIS (not proven by Agda):
- **α⁻¹ = 137.036** — That the K₄ formula IS the fine structure constant
- **τ = 13.7 Gyr** — That N × t_Planck IS the cosmic age
- **Λ-dilution** — The physical mechanism for the 10⁻¹²² ratio
- **K₄ ↔ Universe** — That K₄ structure IS physical spacetime

**The mathematics is proven. The physics correspondence is testable hypothesis.**

---

## What we do NOT predict

- Particle masses (requires matter sector)
- Standard Model gauge groups (requires extension)
- Dark matter distribution (requires cosmological integration)
- (g-2)/2 anomaly (requires QED loop calculation)

FD derives **spacetime geometry** and **spinor structure**. Detailed matter content is a separate question.

---

## Dirac Equation ↔ K₄ Correspondence

The Dirac equation emerges naturally from K₄:

| Dirac Structure | K₄ Origin |
|-----------------|-----------|
| 4-component spinor | \|Bool\|² = 2² = 4 |
| 4 γ-matrices | \|V\| = 4 vertices |
| Clifford dim = 16 | 2⁴ = power set of K₄ |
| 6 bivectors (γᵘγᵛ) | \|E\| = 6 edges |
| Signature (−,+,+,+) | Drift asymmetry |
| Spin-1/2 | \|Bool\| = 2 states |
| g = 2 | g = \|Bool\| = 2 |
| 3 space dimensions | λ-multiplicity = 3 |

The Clifford algebra decomposition **1 + 4 + 6 + 4 + 1 = 16** is exactly the binomial expansion C(4,k), where the "6" in the middle equals \|E\| = 6, the number of K₄ edges!

**Interpretation:** The Dirac equation structure shows NUMERICAL COINCIDENCES with K₄. The K₄ numbers are proven; whether they EXPLAIN Dirac or just happen to match is hypothesis.

| Status | Meaning |
|--------|---------|
| DERIVED | Proven theorem in Agda (d=3, signature) |
| MATH FACT | True by combinatorics (C(4,2)=6) |
| NUMERICAL MATCH | Numbers agree, structural link unproven |
| HYPOTHESIS | Physics interpretation of math |

---

[← Back](./)
