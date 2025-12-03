---
layout: default
title: "Chapter 5: The Graph Laplacian"
breadcrumb: <a href="/">Home</a> &gt; <a href="./">Part II</a> &gt; Chapter 5
---

# Chapter 5: The Graph Laplacian

> *"Can one hear the shape of a drum?"*  
> — Mark Kac (1966)

The graph Laplacian is a matrix that encodes the combinatorial structure of a graph. Its eigenvalues and eigenvectors reveal deep geometric information. In this chapter, we construct the Laplacian of K₄ and prove that its eigenvalues are {0, 4, 4, 4}—with the crucial three-fold degeneracy that will yield three spatial dimensions.

---

## 5.1 The Laplacian in Continuous Mathematics

Before discussing the graph Laplacian, let us recall the continuous Laplacian from differential geometry.

On a Riemannian manifold (M, g), the Laplace-Beltrami operator Δ acts on functions f: M → ℝ:

$$\Delta f = \text{div}(\text{grad } f)$$

In Euclidean coordinates on ℝⁿ:

$$\Delta f = \sum_{i=1}^{n} \frac{\partial^2 f}{\partial x_i^2}$$

The eigenvalues of Δ (on a compact manifold with appropriate boundary conditions) encode geometric information: volume, surface area, dimension, curvature. This is the content of *spectral geometry*.

Kac's famous question—"Can one hear the shape of a drum?"—asks whether the eigenvalues of Δ uniquely determine the shape of a domain. The answer is generally no (there exist isospectral non-isometric manifolds), but the eigenvalues nonetheless carry substantial geometric content.

---

## 5.2 The Graph Laplacian

For a finite graph G = (V, E), we define a discrete analog of the Laplacian.

<div class="definition">
  <strong>Definition (Graph Laplacian)</strong>
  <p>The <strong>graph Laplacian</strong> L of a graph G is the matrix:</p>
  <p style="text-align: center;">$$L = D - A$$</p>
  <p>where:</p>
  <ul>
    <li><strong>D</strong> is the <strong>degree matrix</strong>: D<sub>ii</sub> = deg(v<sub>i</sub>), D<sub>ij</sub> = 0 for i ≠ j</li>
    <li><strong>A</strong> is the <strong>adjacency matrix</strong>: A<sub>ij</sub> = 1 if (v<sub>i</sub>, v<sub>j</sub>) ∈ E, 0 otherwise</li>
  </ul>
</div>

Equivalently:

$$L_{ij} = \begin{cases}
\deg(v_i) & \text{if } i = j \\
-1 & \text{if } (v_i, v_j) \in E \\
0 & \text{otherwise}
\end{cases}$$

### Properties of the Graph Laplacian

<div class="theorem">
  <strong>Theorem (Laplacian Properties)</strong>
  <p>For any graph G:</p>
  <ol>
    <li>L is symmetric: L<sub>ij</sub> = L<sub>ji</sub></li>
    <li>L is positive semi-definite: all eigenvalues ≥ 0</li>
    <li>Row sums are zero: ∑<sub>j</sub> L<sub>ij</sub> = 0 for all i</li>
    <li>λ = 0 is always an eigenvalue, with eigenvector (1, 1, …, 1)</li>
    <li>The multiplicity of λ = 0 equals the number of connected components</li>
  </ol>
</div>

Property 4 is especially important: the "zero mode" corresponds to the constant function on the graph, representing global translation invariance.

---

## 5.3 The Laplacian of K₄

For the complete graph K₄:
- Every vertex has degree 3 (connected to 3 other vertices)
- Every off-diagonal entry is −1 (all pairs adjacent)

Therefore:

$$L_{K_4} = \begin{pmatrix}
3 & -1 & -1 & -1 \\
-1 & 3 & -1 & -1 \\
-1 & -1 & 3 & -1 \\
-1 & -1 & -1 & 3
\end{pmatrix}$$

This matrix is beautiful in its symmetry. It can be written as:

$$L_{K_4} = 4I - J$$

where I is the 4 × 4 identity matrix and J is the 4 × 4 all-ones matrix.

### Agda Formalization

<div class="agda-proof">
  <h4>Laplacian Matrix Definition</h4>

```agda
-- The Laplacian as a function K4Vertex -> K4Vertex -> Int
Laplacian : K4Vertex -> K4Vertex -> Int
-- Diagonal entries: degree = 3
Laplacian v0 v0 = +3
Laplacian v1 v1 = +3
Laplacian v2 v2 = +3
Laplacian v3 v3 = +3
-- Off-diagonal entries: -1 (all pairs adjacent)
Laplacian v0 v1 = -1    Laplacian v0 v2 = -1    Laplacian v0 v3 = -1
Laplacian v1 v0 = -1    Laplacian v1 v2 = -1    Laplacian v1 v3 = -1
Laplacian v2 v0 = -1    Laplacian v2 v1 = -1    Laplacian v2 v3 = -1
Laplacian v3 v0 = -1    Laplacian v3 v1 = -1    Laplacian v3 v2 = -1
```
</div>

<div class="agda-proof">
  <h4>Symmetry Proof</h4>

```agda
-- THEOREM: The Laplacian is symmetric
theorem-Laplacian-symmetric : forall i j -> Laplacian i j == Laplacian j i
theorem-Laplacian-symmetric v0 v0 = refl
theorem-Laplacian-symmetric v0 v1 = refl   -- -1 == -1
theorem-Laplacian-symmetric v0 v2 = refl
theorem-Laplacian-symmetric v0 v3 = refl
theorem-Laplacian-symmetric v1 v0 = refl
theorem-Laplacian-symmetric v1 v1 = refl
-- ... all 16 cases, all by refl
```
</div>

---

## 5.4 Computing the Eigenvalues

To find the eigenvalues of L<sub>K₄</sub>, we solve det(L − λI) = 0.

Using the structure L = 4I − J:

$$L - \lambda I = (4 - \lambda)I - J$$

The eigenvalues of J (the all-ones matrix) are:
- μ₁ = 4 with eigenvector (1, 1, 1, 1) (the row sums)
- μ₂ = μ₃ = μ₄ = 0 with eigenvectors orthogonal to (1, 1, 1, 1)

Since L = 4I − J:
- λ₁ = 4 − 4 = 0 (corresponding to eigenvector (1, 1, 1, 1))
- λ₂ = λ₃ = λ₄ = 4 − 0 = 4 (three-fold degeneracy)

<div class="theorem">
  <strong>Theorem (Eigenvalues of L<sub>K₄</sub>)</strong>
  <p>The eigenvalues of the K₄ Laplacian are:</p>
  <p style="text-align: center;">$$\lambda = \{0, 4, 4, 4\}$$</p>
  <p>with multiplicities 1 and 3 respectively.</p>
</div>

This three-fold degeneracy is the *central result* of DRIFE's spectral analysis. It is not assumed—it is computed from the structure of K₄, which was itself derived from the unavoidability of distinction.

### Agda Verification

<div class="agda-proof">
  <h4>Eigenvalue Verification</h4>

```agda
-- The eigenvalues
lambda0 : Int
lambda0 = 0

lambda4 : Int
lambda4 = +4

-- Zero eigenvector: constant function
zero-eigenvector : K4Vertex -> Int
zero-eigenvector _ = +1   -- (1, 1, 1, 1)

-- THEOREM: zero-eigenvector has eigenvalue 0
-- (L * v)_i = sum_j L_ij * v_j = 3*1 + (-1)*1 + (-1)*1 + (-1)*1 = 0
theorem-zero-eigenvalue : forall v -> 
  matrix-vector-mult Laplacian zero-eigenvector v == 0
theorem-zero-eigenvalue v0 = refl   -- 3 - 1 - 1 - 1 = 0
theorem-zero-eigenvalue v1 = refl
theorem-zero-eigenvalue v2 = refl
theorem-zero-eigenvalue v3 = refl
```
</div>

---

## 5.5 The Meaning of the Three-Fold Degeneracy

Why does the eigenvalue λ = 4 have multiplicity 3? And why does this matter?

### Degeneracy and Symmetry

In physics and mathematics, eigenvalue degeneracy is intimately connected to *symmetry*. When a system has a symmetry group G, the eigenspaces of symmetric operators decompose into irreducible representations of G.

K₄ has the full symmetric group S₄ as its automorphism group (24 elements). The vertex permutations act on functions f: V → ℝ. The eigenspace for λ = 0 is the trivial representation (1-dimensional, symmetric under all permutations). The eigenspace for λ = 4 is the standard representation (3-dimensional).

The dimension 3 is not arbitrary—it is determined by the representation theory of S₄.

### Dimension as Degeneracy

Here is the key insight: the **spatial dimension** equals the **degeneracy of the non-zero eigenvalue**.

<div class="principle-box">
  <h4>Spectral Dimension Principle</h4>
  <p>For a graph G with Laplacian L, the effective embedding dimension is the multiplicity of the first non-zero eigenvalue (the Fiedler eigenvalue multiplicity).</p>
</div>

For K₄:
- First non-zero eigenvalue: λ = 4
- Multiplicity: 3
- Therefore: embedding dimension = 3

This is how three spatial dimensions emerge from pure distinction.

---

## 5.6 The Trace and Curvature

There is an elegant consistency check. The trace of L<sub>K₄</sub> equals the sum of eigenvalues:

$$\text{tr}(L_{K_4}) = 3 + 3 + 3 + 3 = 12 = 0 + 4 + 4 + 4 = \sum \lambda_i$$

This confirms our eigenvalue calculation.

Furthermore, the Ricci scalar (which we will derive later) is:

$$R = 12$$

This is not a coincidence. The trace of the Laplacian is intimately connected to curvature.

---

## 5.7 Summary

We have constructed the graph Laplacian of K₄ and computed its eigenvalues:

$$\lambda = \{0, 4, 4, 4\}$$

The three-fold degeneracy of λ = 4 is the spectral signature of three-dimensional space. In the next chapter, we will construct the actual eigenvectors and use them to embed K₄ in ℝ³.

| Property | Value | Significance |
|----------|-------|--------------|
| Zero eigenvalue | λ₀ = 0 | Global translation mode |
| Nonzero eigenvalue | λ = 4 | Spatial structure |
| Multiplicity | 3 | **Spatial dimension** |
| Trace | 12 | Related to scalar curvature |

---

<nav class="chapter-nav">
  <a href="chapter-04" class="prev">← Chapter 4: K₄</a>
  <a href="chapter-06" class="next">Chapter 6: Three Dimensions →</a>
</nav>
