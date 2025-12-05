---
layout: default
title: For Physicists
---

# For Physicists

**You know the equations. We show where they come from.**

---

## What You Take For Granted

Every physics textbook assumes these. None explains why.

| What you use | What you assume | Why? |
|--------------|-----------------|------|
| $G_{\mu\nu} + \Lambda g_{\mu\nu} = \kappa T_{\mu\nu}$ | Einstein equations | "Nature works this way" |
| $d = 3$ spatial dimensions | 3D manifold | "We observe 3D" |
| $(-,+,+,+)$ signature | Lorentzian metric | "Time is different" |
| $\Lambda > 0$ | Positive cosmological constant | "Dark energy" |
| $\kappa = 8\pi G$ | Coupling constant | "Fit to Newton" |
| $\alpha^{-1} \approx 137$ | Fine structure constant | "Measured" |

These are **inputs** to your theory. You cannot derive them from GR itself.

---

## What We Derive

From a single premise — *distinction exists* — we derive:

| Quantity | FD derivation | Result | Observation |
|----------|---------------|--------|-------------|
| Spatial dimension | K₄ Laplacian eigenspace | **d = 3** | 3 ✓ |
| Time dimension | Drift irreversibility | **1** | 1 ✓ |
| Signature | Symmetric vs asymmetric | **(−,+,+,+)** | (−,+,+,+) ✓ |
| Λ sign | K₄ Ricci trace | **Λ > 0** | Λ > 0 ✓ |
| κ value | Bool × K₄ vertices | **κ = 8** | 8πG ✓ |
| α⁻¹ | λ³χ + deg² + V/111 | **137.036** | 137.036 ✓ |
| Cosmic age | 5 × 4¹⁰⁰ Planck times | **13.73 Gyr** | 13.79 Gyr |

---

## The Bridge: Your Language, Our Structure

### Einstein Equations

**Your version:**
$$G_{\mu\nu} + \Lambda g_{\mu\nu} = \kappa T_{\mu\nu}$$

**Our derivation:**
- $G_{\mu\nu}$ = Ricci curvature of K₄ Laplacian (§ 14-16)
- $\Lambda = 3$ in Planck units, from Tr(L) of K₄ (§ 22b)
- $\kappa = 8$ = |Bool| × |K₄ vertices| = 2 × 4 (§ 18b)
- $T_{\mu\nu}$ = deviation from vacuum K₄ metric

The equations are **identical**. The difference: we derive the constants, you measure them.

---

### Why 3+1 Dimensions?

**Your answer:** "We observe 3 space + 1 time."

**Our derivation:**

1. K₄ (complete graph on 4 vertices) has Laplacian eigenvalues {0, 4, 4, 4}
2. The eigenvalue 4 has **multiplicity 3**
3. Three linearly independent eigenvectors → **3D space**
4. The drift process (D₀ → D₁ → D₂ → D₃) is irreversible → **1D time**

This is not "because we observe it." It's because **4 vertices, fully connected, have this spectrum**.

---

### Why Lorentzian Signature?

**Your answer:** "Time behaves differently from space."

**Our derivation:**

- **Space** comes from K₄ edges (symmetric relations): $+1$ contribution
- **Time** comes from drift (asymmetric process): $-1$ contribution

The minus sign is not a choice. It reflects:
- Edges: bidirectional → positive definite
- Drift: unidirectional → negative contribution

---

### Why κ = 8?

**Your version:** $\kappa = 8\pi G/c^4$ (fitted to Newtonian limit)

**Our derivation:**

$$\kappa = \text{states per distinction} \times \text{distinctions in K₄} = 2 \times 4 = 8$$

Where:
- 2 = |Bool| = states of a single distinction (φ, ¬φ)
- 4 = |K₄| = vertices in the stable graph

The factor $\pi G/c^4$ is **unit conversion**, not physics. In Planck units, κ = 8 exactly.

---

## What You Cannot Explain (But We Can)

### The Fine Structure Constant

**Your situation:** α⁻¹ = 137.035999... is measured. No theory predicts it.

**Our derivation:**

$$\alpha^{-1} = \lambda^3 \chi + \deg^2 + \frac{V}{\deg(E^2+1)}$$

Where (all from K₄):
- λ = 4 (spectral gap)
- χ = 2 (Euler characteristic)  
- deg = 3 (vertex degree)
- V = 4 (vertices)
- E = 6 (edges)

Calculation:
$$= 4^3 \times 2 + 3^2 + \frac{4}{3 \times 37} = 128 + 9 + 0.036... = 137.036...$$

Match: **0.00003%**

---

### The Cosmological Constant Problem

**Your problem:** Why is Λ_obs/Λ_QFT ~ 10⁻¹²²?

**Our solution:**

1. Λ_bare = 3 (from K₄, Planck units)
2. Curvature scales as [length]⁻²
3. Horizon grows: r_H = N × ℓ_P where N = age in Planck times
4. Dilution: Λ_obs = Λ_bare / N² ~ 3 / (10⁶¹)² ~ 10⁻¹²²

No fine-tuning. Just geometry + time.

---

### The Cosmic Age

**Your situation:** τ ≈ 13.79 Gyr (measured). Why this value?

**Our derivation:**

$$N = 5 \times 4^{100}$$

Where:
- 5 = V + 1 = tetrahedron vertices + centroid (geometrically forced)
- 4 = K₄ vertices (base)
- 100 = E² + κ² = 6² + 8² = 36 + 64 (Pythagorean! information capacity)

Result: τ = N × t_Planck = **13.73 Gyr** (0.4% from observation)

---

## The Honest Part

### What We Claim

- The **structure** of GR (equations, constants, dimensions) follows from distinction.
- This is **machine-verified** in Agda under `--safe --without-K`.
- No free parameters are adjusted to fit data.

### What We Don't Claim

- We don't claim this is "the final theory."
- We don't claim to have derived quantum mechanics (yet).
- The α formula has a correction term whose deeper origin is open.

### What Would Falsify This

- Finding a hole in the Agda proof
- Measuring α⁻¹ ≠ 137.036... with better precision
- Showing K₄ is not the unique stable graph

---

## Verify It Yourself

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K --no-libraries FirstDistinction.agda
```

If it compiles, the derivation is valid.

---

## Next Steps

| If you want... | Go to... |
|----------------|----------|
| All predictions | [→ Predictions](predictions) |
| Formal verification | [→ Verify](verify) |
| The Agda source | [→ FirstDistinction.agda](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.agda) |
| Mathematical details | [→ For Mathematicians](for-mathematicians) |

---

<div class="footer-links">
  <a href="/">← Home</a>
  <a href="for-mathematicians">For Mathematicians →</a>
</div>
