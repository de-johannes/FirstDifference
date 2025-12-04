---
layout: default
title: "Chapter 10: Two Levels of Curvature"
breadcrumb: <a href="/">Home</a> &gt; <a href="./">Part IV</a> &gt; Chapter 10
---

# Chapter 10: Two Levels of Curvature

> *"Curvature is the language in which the physical world speaks to us."*  
> — Attributed to various geometers

In standard general relativity, there is one notion of curvature: the Riemann tensor, derived from the Christoffel symbols, which themselves come from metric derivatives. But FD reveals a deeper structure: there are *two* levels of curvature, with different origins and different physical meanings.

---

## 10.1 The Two Curvatures

FD distinguishes:

1. **Geometric curvature** (from Christoffel symbols): This is the standard Riemannian curvature, measuring how the metric varies from point to point.

2. **Spectral curvature** (from Laplacian eigenvalues): This is the intrinsic curvature of the K₄ graph, encoded in its spectral geometry.

These two curvatures have different origins but combine in the Einstein equations.

---

## 10.2 Geometric Curvature: The Riemann Tensor

The Riemann curvature tensor is defined by:

$$R^\rho{}_{\sigma\mu\nu} = \partial_\mu \Gamma^\rho_{\nu\sigma} - \partial_\nu \Gamma^\rho_{\mu\sigma} + \Gamma^\rho_{\mu\lambda} \Gamma^\lambda_{\nu\sigma} - \Gamma^\rho_{\nu\lambda} \Gamma^\lambda_{\mu\sigma}$$

The Ricci tensor is the contraction:

$$R_{\mu\nu} = R^\rho{}_{\mu\rho\nu}$$

And the Ricci scalar is:

$$R = g^{\mu\nu} R_{\mu\nu}$$

### Geometric Curvature on Uniform K₄

We showed in the previous chapter that the Christoffel symbols vanish on uniform K₄:

$$\Gamma^\rho_{\mu\nu} = 0$$

Therefore, the geometric Riemann tensor also vanishes:

$$R^\rho{}_{\sigma\mu\nu} = 0 - 0 + 0 - 0 = 0$$

And consequently:

$$R^{\text{geom}}_{\mu\nu} = 0, \quad R^{\text{geom}} = 0$$

<div class="theorem">
  <strong>Theorem (Vanishing Geometric Curvature)</strong>
  <p>On uniform K₄, the geometric curvature vanishes:</p>
  <p style="text-align: center;">$$R^{\text{geom}}_{\mu\nu} = 0$$</p>
</div>

This means that *locally*, uniform K₄ is flat. A small patch looks like Minkowski space.

---

## 10.3 Spectral Curvature: The Laplacian Eigenvalues

But K₄ is *not* globally flat. Its global structure is encoded in the Laplacian eigenvalues:

$$\lambda = \{0, 4, 4, 4\}$$

This spectral information defines a **spectral curvature**:

<div class="definition">
  <strong>Definition (Spectral Ricci Tensor)</strong>
  <p>The spectral Ricci tensor is:</p>
  <p style="text-align: center;">$$R^{\text{spectral}}_{ij} = \lambda_4 \delta_{ij} = 4 \delta_{ij} \quad \text{(spatial components)}$$</p>
  <p>where λ₄ = 4 is the non-zero eigenvalue.</p>
</div>

The spectral Ricci scalar is:

$$R^{\text{spectral}} = \sum_{i=1}^{3} \lambda_4 = 4 + 4 + 4 = 12$$

### Physical Interpretation

What does spectral curvature mean physically?

In continuous Riemannian geometry, the eigenvalues of the Laplace-Beltrami operator encode global properties of the manifold: volume, total curvature, topology. The famous Weyl asymptotic formula relates eigenvalues to dimension and volume.

For graphs, the Laplacian eigenvalues encode analogous information. The value λ = 4 for K₄ reflects:
- The "size" of the graph (4 vertices)
- The "connectivity" (complete graph, maximum density)
- The "curvature" (positive, like a sphere)

The spectral curvature R<sup>spectral</sup> = 12 is the discrete analog of the scalar curvature of a round sphere.

---

## 10.4 The Cosmological Constant

The spectral curvature does not vanish—it is a positive constant. This constant has a direct physical interpretation: it is the **cosmological constant** Λ.

<div class="theorem">
  <strong>Theorem (Cosmological Constant from Spectral Curvature)</strong>
  <p>The cosmological constant is:</p>
  <p style="text-align: center;">$$\Lambda = \frac{R^{\text{spectral}}}{4} = \frac{12}{4} = 3$$</p>
  <p>(in Planck units, with appropriate normalization).</p>
</div>

### The Sign of Λ

The cosmological constant Λ = 3 > 0 is *positive*. This is a prediction of FD:

> *The cosmological constant is positive because the spectral curvature of K₄ is positive.*

This matches observation! The universe has a positive cosmological constant ("dark energy"). FD *explains* the sign of Λ from the structure of K₄.

<div class="agda-proof">
  <h4>Cosmological Constant</h4>

```agda
-- Spectral Ricci scalar
spectralRicciScalar : Rational
spectralRicciScalar = 4 + 4 + 4   -- = 12

-- Cosmological constant
cosmologicalConstant : Rational
cosmologicalConstant = spectralRicciScalar / 4   -- = 3

-- THEOREM: Lambda > 0
theorem-Lambda-positive : cosmologicalConstant > 0
theorem-Lambda-positive = 3>0   -- 3 > 0, verified
```
</div>

---

## 10.5 Combining the Two Curvatures

In FD, the total curvature has two sources:
1. Geometric curvature $R^{\text{geom}}_{\mu\nu}$ (from metric derivatives)
2. Spectral curvature, contributing via Λg<sub>μν</sub>

The effective Einstein tensor is:

$$G_{\mu\nu}^{\text{eff}} = G_{\mu\nu} + \Lambda g_{\mu\nu}$$

where $G_{\mu\nu} = R_{\mu\nu} - \frac{1}{2} g_{\mu\nu} R$ is the standard Einstein tensor (from geometric curvature).

On uniform K₄:
- G<sub>μν</sub> = 0 (geometric curvature vanishes)
- Λg<sub>μν</sub> = 3g<sub>μν</sub> (spectral curvature contributes)

So the effective curvature is:

$$G_{\mu\nu}^{\text{eff}} = 3 g_{\mu\nu}$$

This is the curvature of de Sitter space—a spacetime with positive cosmological constant.

---

## 10.6 Summary

| Curvature Type | Source | Value | Physical Meaning |
|----------------|--------|-------|------------------|
| Geometric | Christoffel symbols | 0 | Local flatness |
| Spectral | Laplacian eigenvalues | R = 12 | Global curvature |
| Cosmological constant | R<sup>spectral</sup>/4 | Λ = 3 | Dark energy |

<div class="highlight-box">
  <h4>Two Sources of Curvature</h4>
  <ul>
    <li><strong>Geometric</strong>: vanishes for uniform K₄ → local flatness</li>
    <li><strong>Spectral</strong>: comes from Laplacian → positive Λ → de Sitter geometry</li>
  </ul>
  <p>The separation of these two curvatures is a key insight of FD.</p>
</div>

In the next chapter, we derive the full Einstein field equations with their constants.

---

<nav class="chapter-nav">
  <a href="./" class="prev">← Part IV Overview</a>
  <a href="chapter-11" class="next">Chapter 11: Einstein Equations →</a>
</nav>
