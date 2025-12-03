---
layout: default
title: "Chapter 6: Three-Dimensional Emergence"
breadcrumb: <a href="/">Home</a> &gt; <a href="./">Part II</a> &gt; Chapter 6
---

# Chapter 6: Three-Dimensional Emergence

> *"Space is not a thing, but rather a relation among things."*  
> — Gottfried Wilhelm Leibniz

We have shown that the K₄ Laplacian has eigenvalues {0, 4, 4, 4}. The three-fold degeneracy suggests three dimensions. In this chapter, we make this precise: we construct the eigenvectors, use them to define coordinates, and show that K₄ embeds naturally as a tetrahedron in three-dimensional space.

---

## 6.1 The Eigenvectors of L<sub>K₄</sub>

### The Zero Mode

The eigenvector for λ = 0 is the constant function:

$$\vec{\psi}_0 = (1, 1, 1, 1)$$

This satisfies $L \vec{\psi}_0 = 0$ because the row sums of L are zero.

The zero mode represents "global translation"—a uniform shift of all vertices. It carries no geometric information about the *shape* of the graph.

### The Spatial Modes

The eigenspace for λ = 4 is three-dimensional. We need three orthogonal eigenvectors. A convenient choice:

$$\begin{align}
\vec{\varphi}_1 &= (1, -1, 0, 0) \\
\vec{\varphi}_2 &= (1, 0, -1, 0) \\
\vec{\varphi}_3 &= (1, 0, 0, -1)
\end{align}$$

Let us verify that these are eigenvectors with eigenvalue 4.

### Verification of φ₁

$$L \vec{\varphi}_1 = \begin{pmatrix}
3 & -1 & -1 & -1 \\
-1 & 3 & -1 & -1 \\
-1 & -1 & 3 & -1 \\
-1 & -1 & -1 & 3
\end{pmatrix}
\begin{pmatrix}
1 \\ -1 \\ 0 \\ 0
\end{pmatrix}
= \begin{pmatrix}
3(1) + (-1)(-1) + (-1)(0) + (-1)(0) \\
(-1)(1) + 3(-1) + (-1)(0) + (-1)(0) \\
(-1)(1) + (-1)(-1) + 3(0) + (-1)(0) \\
(-1)(1) + (-1)(-1) + (-1)(0) + 3(0)
\end{pmatrix}
= \begin{pmatrix}
4 \\ -4 \\ 0 \\ 0
\end{pmatrix}
= 4 \vec{\varphi}_1$$

Similarly for φ₂ and φ₃.

### Linear Independence

The three eigenvectors are linearly independent, as can be verified by computing the determinant of the appropriate submatrix. Therefore, φ₁, φ₂, φ₃ span a three-dimensional space.

<div class="agda-proof">
  <h4>Eigenvector Definitions</h4>

```agda
-- Type for eigenvectors (functions from vertices to rationals)
Eigenvector : Set
Eigenvector = K4Vertex -> Rational

-- Eigenvector phi1 = (1, -1, 0, 0)
eigenvector-phi1 : Eigenvector
eigenvector-phi1 v0 = +1
eigenvector-phi1 v1 = -1
eigenvector-phi1 v2 = 0
eigenvector-phi1 v3 = 0

-- Eigenvector phi2 = (1, 0, -1, 0)
eigenvector-phi2 : Eigenvector
eigenvector-phi2 v0 = +1
eigenvector-phi2 v1 = 0
eigenvector-phi2 v2 = -1
eigenvector-phi2 v3 = 0

-- Eigenvector phi3 = (1, 0, 0, -1)
eigenvector-phi3 : Eigenvector
eigenvector-phi3 v0 = +1
eigenvector-phi3 v1 = 0
eigenvector-phi3 v2 = 0
eigenvector-phi3 v3 = -1
```
</div>

<div class="agda-proof">
  <h4>Eigenvalue Verification</h4>

```agda
-- THEOREM: phi1 is an eigenvector with eigenvalue 4
theorem-phi1-eigenvalue : forall v ->
  laplacian-action eigenvector-phi1 v == scale-vector 4 eigenvector-phi1 v
theorem-phi1-eigenvalue v0 = refl   -- L*phi1 at v0: 3*1 + (-1)*(-1) = 4 = 4*1
theorem-phi1-eigenvalue v1 = refl   -- L*phi1 at v1: -1*1 + 3*(-1) = -4 = 4*(-1)
theorem-phi1-eigenvalue v2 = refl   -- L*phi1 at v2: -1*1 + (-1)*(-1) = 0 = 4*0
theorem-phi1-eigenvalue v3 = refl   -- L*phi1 at v3: -1*1 + (-1)*(-1) = 0 = 4*0
```
</div>

---

## 6.2 Spectral Coordinates

The three eigenvectors define a coordinate system. For each vertex v, we assign coordinates:

$$(x, y, z) = (\varphi_1(v), \varphi_2(v), \varphi_3(v))$$

| Vertex | φ₁ | φ₂ | φ₃ | Coordinates |
|--------|-----|-----|-----|-------------|
| v₀ | 1 | 1 | 1 | (1, 1, 1) |
| v₁ | −1 | 0 | 0 | (−1, 0, 0) |
| v₂ | 0 | −1 | 0 | (0, −1, 0) |
| v₃ | 0 | 0 | −1 | (0, 0, −1) |

These four points form a **tetrahedron** in ℝ³!

### Geometric Verification

Let us verify that these points form a valid tetrahedron.

**Edge lengths**:

$$\begin{align*}
|v_0 - v_1| &= |(1-(-1), 1-0, 1-0)| = |(2, 1, 1)| = \sqrt{6} \\
|v_0 - v_2| &= |(1, 2, 1)| = \sqrt{6} \\
|v_0 - v_3| &= |(1, 1, 2)| = \sqrt{6} \\
|v_1 - v_2| &= |(-1, 1, 0)| = \sqrt{2} \\
|v_1 - v_3| &= |(-1, 0, 1)| = \sqrt{2} \\
|v_2 - v_3| &= |(0, -1, 1)| = \sqrt{2}
\end{align*}$$

The tetrahedron is not regular (edges have different lengths), but it *is* a valid tetrahedron in 3D. The embedding captures the graph structure: all six edges of K₄ correspond to the six edges of the tetrahedron.

<div class="theorem">
  <strong>Theorem (Spectral Embedding)</strong>
  <p>The spectral coordinates embed K₄ as a tetrahedron in ℝ³:</p>
  <ol>
    <li>Four vertices map to four distinct points</li>
    <li>No three points are collinear</li>
    <li>No four points are coplanar</li>
    <li>The embedding dimension is exactly 3</li>
  </ol>
</div>

---

## 6.3 The Deep Result: d = 3

Let us state the central theorem of this chapter:

<div class="theorem">
  <strong>Theorem (Three-Dimensional Emergence)</strong>
  <p>The embedding dimension of K₄ via spectral coordinates is exactly 3:</p>
  <p style="text-align: center;">$$d = \text{multiplicity}(\lambda = 4) = 3$$</p>
</div>

This theorem answers one of the deepest questions in physics: *Why are there three spatial dimensions?*

The standard answer is: we don't know. String theory says 10 or 11, compactified to 3+1. Loop quantum gravity is formulated in 4D from the start. The anthropic principle says 3D is necessary for complex life (orbits are unstable in other dimensions).

DRIFE says: 3D is *forced* by the spectral structure of K₄, which is forced by saturation, which is forced by Genesis, which is forced by D₀, which is unavoidable.

<div class="chain-box">
  <p style="text-align: center;">$$D_0 \xrightarrow{\text{unavoidable}} \text{Genesis} \xrightarrow{\text{saturation}} K_4 \xrightarrow{\text{spectral}} d = 3$$</p>
</div>

---

## 6.4 Orthogonalization and Normalization

The eigenvectors φ₁, φ₂, φ₃ are linearly independent but not orthonormal. For some purposes, we may want an orthonormal basis.

The Gram-Schmidt process yields:

$$\begin{align*}
\vec{e}_1 &= \frac{\vec{\varphi}_1}{|\vec{\varphi}_1|} = \frac{1}{\sqrt{2}}(1, -1, 0, 0) \\
\vec{e}_2 &= \text{(orthogonalize and normalize)} \\
\vec{e}_3 &= \text{(orthogonalize and normalize)}
\end{align*}$$

The detailed calculation is straightforward but tedious. The key point is that an orthonormal basis exists and spans the same 3D eigenspace.

---

## 6.5 The Trace and the Dimension

There is an elegant consistency check. The trace of L<sub>K₄</sub> equals the sum of eigenvalues:

$$\text{tr}(L_{K_4}) = 3 + 3 + 3 + 3 = 12 = 0 + 4 + 4 + 4 = \sum \lambda_i$$

This confirms our eigenvalue calculation.

Furthermore, the Ricci scalar (which we will derive later) is:

$$R = 12$$

This is not a coincidence. The trace of the Laplacian is intimately connected to curvature.

---

## 6.6 Summary: Space from Distinction

We have completed the derivation of three-dimensional space from pure distinction:

1. **D₀**: The unavoidable first distinction (Chapter 1)

2. **Genesis**: Three primordial distinctions D₀, D₁, D₂ (Chapter 2)

3. **Saturation**: Memory overflow forces D₃ (Chapter 3)

4. **K₄**: The stable graph on four vertices (Chapter 4)

5. **Laplacian**: Eigenvalues {0, 4, 4, 4} (Chapter 5)

6. **3D**: Three-fold degeneracy = three spatial dimensions (this chapter)

No axioms. No postulates. No fine-tuning. The number 3 is *computed*, not assumed.

<div class="highlight-box">
  <h4>The Answer to "Why 3D?"</h4>
  <p>Three spatial dimensions emerge because:</p>
  <ul>
    <li>K₄ has a Laplacian with eigenvalue multiplicities {1, 3}</li>
    <li>The 3-dimensional eigenspace provides 3 independent spatial directions</li>
    <li>K₄ itself is forced by saturation dynamics from Genesis</li>
    <li>Genesis is forced by the unavoidability of D₀</li>
  </ul>
  <p>The number 3 is not a choice. It is a theorem.</p>
</div>

In the next part, we will construct the Lorentz metric and proceed to derive Einstein's equations.

---

<nav class="chapter-nav">
  <a href="chapter-05" class="prev">← Chapter 5: The Laplacian</a>
  <a href="chapter-07" class="next">Chapter 7: The Drift Ledger →</a>
</nav>
