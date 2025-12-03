---
layout: default
title: "Appendix A: Agda Code Reference"
breadcrumb: <a href="/">Home</a> &gt; <a href="./">Appendices</a> &gt; Appendix A
---

# Appendix A: Agda Code Reference

The complete Agda proof is available at:

**[github.com/de-johannes/FirstDifference](https://github.com/de-johannes/FirstDifference)**

---

## Verification

To verify the proofs:

```bash
agda --safe --without-K --no-libraries DRIFE.agda
```

The flags ensure:
- `--safe`: No postulates or escape hatches
- `--without-K`: Compatible with homotopy type theory
- `--no-libraries`: No external dependencies

---

## Key Functions

| Function | Description |
|----------|-------------|
| `unavoidability-of-D0` | Proves D₀ cannot be coherently denied |
| `theorem-D3-emerges` | Proves D₃ is forced by saturation |
| `theorem-k4-has-6-edges` | Proves K₄ structure |
| `theorem-eigenvector-*` | Proves eigenvalue equations |
| `theorem-3D` | Proves embedding dimension is 3 |
| `theorem-christoffel-vanishes` | Proves Γ = 0 for uniform K₄ |
| `theorem-kappa-is-eight` | Proves κ = 8 |
| `ultimate-theorem` | The main result |

---

## Code Structure

```
DRIFE.agda
├── Distinction definition
├── Genesis construction  
├── Saturation and D3 forcing
├── K4 graph definition
├── Laplacian construction
├── Eigenvalue proofs
├── Spacetime structure
├── Metric tensor
├── Einstein equations
└── Ultimate theorem
```

---

## Statistics

- **Total lines**: 6,516
- **Theorems**: 47
- **Type-checked**: Yes
- **External dependencies**: None

---

<nav class="chapter-nav">
  <a href="./" class="prev">← Appendices</a>
  <a href="appendix-b" class="next">Appendix B →</a>
</nav>
