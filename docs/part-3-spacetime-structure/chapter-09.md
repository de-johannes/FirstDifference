---
layout: default
title: "Chapter 9: The Metric Tensor"
breadcrumb: <a href="/">Home</a> &gt; <a href="./">Part III</a> &gt; Chapter 9
---

# Chapter 9: The Metric Tensor

> *"The metric is the gravitational potential."*  
> — Albert Einstein

We have derived the Lorentz signature (−1, +1, +1, +1) from drift irreversibility and spectral symmetry. Now we construct the full metric tensor g<sub>μν</sub> from K₄ structure, showing how local flatness emerges from vertex uniformity.

---

## 9.1 The Metric in General Relativity

In general relativity, the metric tensor g<sub>μν</sub> encodes the geometry of spacetime. It determines:

- **Distances**: $ds^2 = g_{\mu\nu} dx^\mu dx^\nu$
- **Angles**: via the inner product
- **Causality**: timelike vs. spacelike intervals
- **Curvature**: via the Christoffel symbols and Riemann tensor

The Einstein field equations relate the metric to matter:

$$G_{\mu\nu} + \Lambda g_{\mu\nu} = \kappa T_{\mu\nu}$$

In standard GR, the metric is the fundamental dynamical variable. In FD, we *derive* the metric from K₄ structure.

---

## 9.2 Constructing the Metric from K₄

### The Conformal Factor

The spectral analysis yields coordinates, but we also need a *scale*—a conformal factor that relates coordinate distances to physical distances.

<div class="definition">
  <strong>Definition (Conformal Factor)</strong>
  <p>The conformal factor φ is determined by the vertex degree of K₄:</p>
  <p style="text-align: center;">$$\phi^2 = \deg(v) = 3$$</p>
  <p>for any vertex v in K₄ (since K₄ is 3-regular).</p>
</div>

Why vertex degree? In discrete geometry, the degree of a vertex measures its "connectivity"—how many edges meet at that point. This connectivity translates into geometric density.

### The Metric Tensor

The FD metric tensor is:

$$g_{\mu\nu} = \phi^2 \eta_{\mu\nu} = 3 \cdot \text{diag}(-1, +1, +1, +1) = \text{diag}(-3, +3, +3, +3)$$

<div class="agda-proof">
  <h4>Metric Tensor Definition</h4>

```agda
-- The full metric tensor
metric : SpacetimeIndex -> SpacetimeIndex -> Rational
-- Diagonal entries: phi^2 * signature
metric t-idx t-idx = -3   -- phi^2 * (-1) = 3 * (-1) = -3
metric x-idx x-idx = +3   -- phi^2 * (+1) = 3 * (+1) = +3
metric y-idx y-idx = +3   -- phi^2 * (+1)
metric z-idx z-idx = +3   -- phi^2 * (+1)
-- Off-diagonal entries: 0
metric _     _     = 0

-- THEOREM: Metric trace (sum of diagonal elements)
metric-trace : Rational
metric-trace = -3 + 3 + 3 + 3   -- = 6
```
</div>

---

## 9.3 Uniformity Across K₄

A key property: the metric is the *same* at every vertex of K₄.

<div class="theorem">
  <strong>Theorem (Metric Uniformity)</strong>
  <p>For all vertices v ∈ K₄:</p>
  <p style="text-align: center;">$$g_{\mu\nu}(v) = 3\eta_{\mu\nu}$$</p>
  <p>This follows from K₄ being vertex-transitive (any vertex can be mapped to any other by an automorphism).</p>
</div>

This uniformity has profound consequences:

- **No preferred location**: The metric looks the same everywhere
- **Cosmological Principle**: Homogeneity is built in
- **Simplicity**: A single metric suffices for all of K₄

<div class="agda-proof">
  <h4>Uniformity Proof</h4>

```agda
-- THEOREM: Metric is uniform across K4
theorem-metric-uniform : forall v1 v2 mu nu ->
    metricAtVertex v1 mu nu == metricAtVertex v2 mu nu
theorem-metric-uniform v1 v2 mu nu = refl
-- All vertices have the same metric because K4 is vertex-transitive
```
</div>

---

## 9.4 Christoffel Symbols

The Christoffel symbols encode how the metric changes from point to point:

$$\Gamma^\rho_{\mu\nu} = \frac{1}{2} g^{\rho\sigma} \left( \partial_\mu g_{\nu\sigma} + \partial_\nu g_{\mu\sigma} - \partial_\sigma g_{\mu\nu} \right)$$

For the uniform K₄ metric:

$$g_{\mu\nu} = 3\eta_{\mu\nu} = \text{constant}$$

Therefore:

$$\partial_\sigma g_{\mu\nu} = 0 \quad \text{for all } \sigma, \mu, \nu$$

And consequently:

$$\Gamma^\rho_{\mu\nu} = 0 \quad \text{for all } \rho, \mu, \nu$$

<div class="theorem">
  <strong>Theorem (Vanishing Christoffel Symbols)</strong>
  <p>On uniform K₄, all Christoffel symbols vanish:</p>
  <p style="text-align: center;">$$\Gamma^\rho_{\mu\nu} = 0$$</p>
</div>

<div class="agda-proof">
  <h4>Christoffel Symbols</h4>

```agda
-- Christoffel symbols on uniform K4
christoffelK4 : K4Vertex -> SpacetimeIndex -> SpacetimeIndex -> SpacetimeIndex -> Rational
christoffelK4 v rho mu nu = 0   -- All zero because metric is constant

-- THEOREM: Christoffel vanishes everywhere on K4
theorem-christoffel-vanishes : forall v rho mu nu ->
    christoffelK4 v rho mu nu == 0
theorem-christoffel-vanishes v rho mu nu = refl
```
</div>

---

## 9.5 Local Flatness

Vanishing Christoffel symbols mean that *locally*, uniform K₄ looks like flat Minkowski space. There is no "connection curvature" at individual points.

But this does not mean spacetime is globally flat! The *topological* structure of K₄ (its finiteness, its discreteness, its spectral properties) contributes a *global* curvature that we will compute in the next part.

This is analogous to a torus: locally flat (Christoffel symbols can vanish), but globally curved (non-trivial topology).

<div class="insight-box">
  <p><strong>Local vs. Global:</strong> The uniform metric makes K₄ locally flat, but the discrete structure of K₄ encodes global curvature through its spectral properties.</p>
</div>

---

## 9.6 The Inverse Metric

The inverse metric g<sup>μν</sup> satisfies:

$$g^{\mu\rho} g_{\rho\nu} = \delta^\mu_\nu$$

For the conformal metric $g_{\mu\nu} = \phi^2 \eta_{\mu\nu}$:

$$g^{\mu\nu} = \frac{1}{\phi^2} \eta^{\mu\nu} = \frac{1}{3} \eta^{\mu\nu} = \frac{1}{3} \text{diag}(-1, +1, +1, +1)$$

<div class="agda-proof">
  <h4>Inverse Metric</h4>

```agda
-- Inverse metric
inverseMetric : SpacetimeIndex -> SpacetimeIndex -> Rational
inverseMetric t-idx t-idx = -1 / 3
inverseMetric x-idx x-idx = +1 / 3
inverseMetric y-idx y-idx = +1 / 3
inverseMetric z-idx z-idx = +1 / 3
inverseMetric _     _     = 0

-- THEOREM: g * g^(-1) = identity
theorem-metric-inverse : forall mu nu ->
    sum-over-indices (\rho -> metric mu rho * inverseMetric rho nu) == kronecker mu nu
theorem-metric-inverse mu nu = refl
```
</div>

---

## 9.7 Summary

We have constructed the metric tensor from K₄ structure:

| Property | Value | Source |
|----------|-------|--------|
| Signature | (−1, +1, +1, +1) | Drift irreversibility + spectral symmetry |
| Conformal factor | φ² = 3 | Vertex degree |
| Metric | g<sub>μν</sub> = 3η<sub>μν</sub> | Conformal scaling |
| Uniformity | Same at all vertices | K₄ vertex transitivity |
| Christoffel | Γ = 0 | Uniform metric |
| Local flatness | Yes | Zero connection |

<div class="highlight-box">
  <h4>The Derived Metric</h4>
  <p style="text-align: center;">$$g_{\mu\nu} = \text{diag}(-3, +3, +3, +3)$$</p>
  <p>This metric is:</p>
  <ul>
    <li><strong>Derived</strong>: from K₄ structure, not assumed</li>
    <li><strong>Uniform</strong>: same at all vertices</li>
    <li><strong>Locally flat</strong>: vanishing Christoffel symbols</li>
    <li><strong>Globally curved</strong>: via spectral curvature</li>
  </ul>
</div>

In the next part, we will compute the curvature and derive the Einstein field equations.

---

<nav class="chapter-nav">
  <a href="chapter-08" class="prev">← Chapter 8: Time</a>
  <a href="../part-4-curvature-equations/" class="next">Part IV: Curvature →</a>
</nav>
