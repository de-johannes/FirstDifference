---
layout: default
title: "Appendix B: Python Validation"
breadcrumb: <a href="/">Home</a> &gt; <a href="./">Appendices</a> &gt; Appendix B
---

# Appendix B: Python Validation

Python scripts provide numerical verification of K₄ properties and FD predictions.

---

## Running the Validation

```bash
python3 validate_K4.py
```

**Output**:
```
7/7 tests passed
d=3, Lambda>0, kappa=8, R=12
```

---

## What Is Tested

| Test | Expected | Verified |
|------|----------|----------|
| Eigenvalues of L<sub>K₄</sub> | {0, 4, 4, 4} | ✓ |
| Spatial dimension | d = 3 | ✓ |
| Cosmological constant sign | Λ > 0 | ✓ |
| Coupling constant | κ = 8 | ✓ |
| Ricci scalar | R = 12 | ✓ |
| Euler characteristic | χ = 2 | ✓ |
| Signature trace | tr(η) = 2 | ✓ |

---

## Sample Code

```python
import numpy as np

# K4 Laplacian matrix
L = np.array([
    [ 3, -1, -1, -1],
    [-1,  3, -1, -1],
    [-1, -1,  3, -1],
    [-1, -1, -1,  3]
])

# Compute eigenvalues
eigenvalues = np.linalg.eigvalsh(L)
print(f"Eigenvalues: {sorted(eigenvalues)}")
# Output: [0, 4, 4, 4]

# Spatial dimension = multiplicity of nonzero eigenvalue
d = np.sum(np.isclose(eigenvalues, 4))
print(f"Spatial dimension: d = {d}")
# Output: d = 3

# Cosmological constant
Lambda = np.sum(eigenvalues) / 4
print(f"Lambda = {Lambda}")
# Output: Lambda = 3.0

# Ricci scalar
R = np.trace(L)
print(f"R = {R}")
# Output: R = 12
```

---

## Additional Scripts

- `validate_K4.py` — Main validation suite
- `validate_lambda.py` — Cosmological constant calculations
- `simulate_collapse.py` — Distinction dynamics simulation

---

<nav class="chapter-nav">
  <a href="appendix-a" class="prev">← Appendix A</a>
  <a href=".." class="next">Home →</a>
</nav>
