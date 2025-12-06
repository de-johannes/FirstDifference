# First Distinction (FD)

[![DOI](https://zenodo.org/badge/1108945544.svg)](https://doi.org/10.5281/zenodo.17826218)
[![Release CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/release-ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/release-ci.yml)
[![Agda](https://img.shields.io/badge/Agda-2.7.0.1-blue)](https://agda.readthedocs.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

**A Graph-Theoretic Exploration of Why K₄ Produces Physics-Like Numbers**

---

## ⚠️ Important Disclaimer

This project proves **graph-theoretic theorems** about K₄ (the complete graph on 4 vertices). The numerical coincidences with physical constants are **striking but unexplained**.

**What IS proven:** K₄ invariants and their algebraic combinations  
**What is NOT claimed:** That this IS physics or explains the universe

The correspondence may be: deep truth, mathematical coincidence, or something else entirely. We present the mathematics; interpretation is left to the reader.

---

## What This Is

A single Agda file (`FirstDistinction.agda`, 12,400+ lines incl. comments) that:

1. **Proves** K₄ emerges from minimal type-theoretic constraints
2. **Computes** algebraic invariants of K₄ (vertices, edges, Euler characteristic, Laplacian, etc.)
3. **Observes** these numbers match physical constants to surprising precision

```
⊤ (unit type exists)
       ↓
Minimal closure under distinction
       ↓
K₄ complete graph (V=4, E=6, χ=2, deg=3)
       ↓
Graph-theoretic invariants match:
  • d = 3 (Laplacian degeneracy)
  • κ = 8 (from χ via Pythagorean)
  • α⁻¹ = 137 (Operad arities)
  • Spinor dimension = 4 (Clifford structure)
  • Particle mass ratios (combinatorial formulas)
```

Machine-checked under `--safe --without-K`. No postulates.

---

## The Construction

```
D₀ (⊤ vs ⊥)               Unit type vs Empty type
       ↓
Genesis (D₀, D₁, D₂)      Closure under distinction
       ↓
Saturation (η = 6)        Complete pairing
       ↓
D₃ emerges                Fourth vertex forced
       ↓
K₄ complete graph         4 vertices, 6 edges
       ↓
Canonical invariants:
  V = 4                   Vertices
  E = 6                   Edges  
  F = 4                   Faces (as tetrahedron)
  χ = 2                   Euler characteristic
  deg = 3                 Vertex degree
  λ = {0,4,4,4}           Laplacian eigenvalues
```

Every step follows from the previous. The mathematics is **proven**, not assumed.

---

## Numerical Coincidences

The following are **proven graph-theoretic facts** about K₄:

| K₄ Property | Computed | Physics Analogue | Match |
|-------------|----------|------------------|-------|
| Laplacian degeneracy | 3 | Spatial dimensions | ✓ |
| Euler char × 4 | 8 | Einstein's κ = 8πG | ✓ |
| Λ = deg | 3 > 0 | Cosmological constant sign | ✓ |
| Operad arities | 137 | Fine structure α⁻¹ | ✓ |
| E² + κ² | 100 = 10² | Pythagorean triple | ✓ |
| Clifford grades | 1,4,6,4,1 | Dirac γ-matrices | ✓ |
| 2^V | 4 | Spinor components | ✓ |

### Mass Ratio Formulas (Combinatorial)

Using only K₄ invariants (V=4, E=6, χ=2, deg=3, α⁻¹=137):

| Particle | Formula | Computed | Experiment | Error |
|----------|---------|----------|------------|-------|
| Proton/electron | χ² × deg³ × F₂ | 1836 | 1836.15 | 0.008% |
| Neutron/electron | proton + χ | 1838 | 1838.68 | 0.04% |
| Muon/electron | deg² × (2^V + V + deg) | 207 | 206.77 | 0.1% |
| Tau/Muon | F₂ = 2^V + 1 | 17 | 16.82 | 1% |
| Top/electron | α⁻² × (F₂ + 1) | 337,842 | 337,900 | 0.02% |

where F₂ = 17 (Fermat prime = 2⁴ + 1)

**These are theorems about K₄ combinatorics.** Why they match experimental mass ratios is unexplained.

---

### Dirac Structure from K₄

The Clifford algebra Cl(1,3) has dimension 16 = 2^V with grade decomposition:
- Grade 0: 1 (identity)
- Grade 1: 4 (γ-matrices) = V
- Grade 2: 6 (bivectors) = E  
- Grade 3: 4 (trivectors) = V
- Grade 4: 1 (pseudoscalar)

**Total: 1 + 4 + 6 + 4 + 1 = 16 = 2^V**

The Dirac spinor has 4 components = V = |K₄|. This is a structural coincidence, not a derivation of the Dirac equation.

---

## Files

```
FirstDifference/
├── FirstDistinction.agda  # The proof (12,400+ lines, --safe --without-K)
├── validate_K4.py         # Numerical validation
├── simulate_collapse.py   # Topological brake visualization
├── docs/                  # Website (GitHub Pages)
└── README.md              # This file
```

---

## Run It

### Verify the proof
```bash
agda --safe --without-K FirstDistinction.agda
```

### Validate numerically
```bash
python3 validate_K4.py
# Output: 7/7 tests passed
```

---

## The Core Question

**Why does K₄ produce numbers that match physics?**

Possibilities:
1. **Deep connection:** The universe *is* structured by K₄ constraints
2. **Mathematical coincidence:** The numbers just happen to match
3. **Selection bias:** We found patterns in hindsight
4. **Something else:** An explanation we haven't thought of

This project doesn't answer this question. It merely demonstrates that the coincidences exist and are mathematically rigorous.

---

## Technical Details

### Agda Flags
- `--safe`: No postulates, no unsafe pragmas
- `--without-K`: No axiom K (compatible with HoTT)

### What's Proven (Graph Theory)
- K₄ emerges from minimal distinction closure
- All K₄ invariants: V=4, E=6, F=4, χ=2, deg=3
- Laplacian eigenvalues {0, 4, 4, 4}
- 3-fold degeneracy of nonzero eigenvalue
- Pythagorean identity: E² + κ² = 6² + 8² = 100 = 10²
- Clifford grade decomposition matches V, E
- Operad arity computation yields 137
- Mass ratio formulas are integer identities

### What's NOT Claimed
- That K₄ "is" spacetime
- That these coincidences have physical meaning
- That the Dirac equation follows from K₄
- That particle masses are "derived"

The formulas compute. The coincidences exist. The interpretation is open.

---

## Philosophy (Speculation)

> *"These are just numbers from a graph. Why do they match reality?"*

We don't know. But the fact that K₄—the simplest complete graph that requires 3D to embed—produces numbers matching 3D physics, electromagnetism (α), gravity (κ), and particle masses is, at minimum, curious.

---

## Citation

```bibtex
@software{first_distinction_2025,
  author = {Wielsch, Johannes},
  title = {First Distinction: K₄ Graph Theory and Physical Constants},
  year = {2025},
  url = {https://github.com/de-johannes/FirstDifference},
  note = {Graph-theoretic exploration, not physics claim}
}
```

---

## License

Code: MIT  
Documentation: CC BY 4.0

---

**The proofs compile. The numbers match. The reason is unknown.**

