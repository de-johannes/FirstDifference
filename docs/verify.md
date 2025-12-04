---
layout: default
title: Verify
---

# Verify

FD is not a claim. It's code that either compiles or doesn't.

---

## Status

[![CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml)

| Check | Status |
|-------|--------|
| `FirstDistinction.agda` compiles | ✓ |
| `--safe` (no unsafe features) | ✓ |
| `--without-K` (no Axiom K dependency) | ✓ |
| `--no-libraries` (no external imports) | ✓ |
| No postulates | ✓ |
| No holes `{!!}` | ✓ |
| Numerical validation | ✓ |

---

## Check it yourself

### 1. Clone the repository

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
```

### 2. Install Agda

```bash
# macOS
brew install agda

# Ubuntu/Debian
sudo apt install agda

# Or via Stack
stack install Agda
```

Version 2.6.3+ recommended.

### 3. Compile

```bash
agda --safe --without-K --no-libraries FirstDistinction.agda
```

If no error message appears: **The proof is valid.**

---

## What do the flags mean?

| Flag | Meaning |
|------|---------|
| `--safe` | No `postulate`, no `TERMINATING` pragmas, no unsafe features |
| `--without-K` | No Axiom K (important for homotopy type theory compatibility) |
| `--no-libraries` | No external libraries — everything self-defined |

This combination is the strictest setting in Agda. If the code compiles, there are no backdoors.

---

## Numerical validation

The Python scripts validate the numerical predictions:

```bash
python src/python/validate_K4.py      # K₄ spectral geometry
python src/python/validate_alpha.py   # Fine structure constant
python src/python/validate_lambda.py  # Cosmological constant
python src/python/validate_cosmic_age.py  # Cosmic age
```

These are **not** part of the formal proof, but demonstrate that the derived values match observations.

---

## Key Theorems

All machine-verified in Agda under `--safe --without-K --no-libraries`:

### Geometry

| Theorem | Statement | Section |
|---------|-----------|---------|
| `theorem-dimension-3` | d = 3 from λ=4 multiplicity | § 11 |
| `theorem-signature` | (−,+,+,+) from drift asymmetry | § 16 |
| `theorem-euler-char` | χ = V − E + F = 2 | § 15 |

### Fine Structure Constant

| Theorem | Statement | Section |
|---------|-----------|---------|
| `theorem-alpha-integer` | α⁻¹ = 137 (integer part) | § 22f |
| `theorem-spectral-term` | λ³χ = 128 | § 22f |
| `theorem-correction-denom` | 4/111 correction | § 22f |

### Cosmic Age N = 5 × 4¹⁰⁰

| Theorem | Statement | Section |
|---------|-----------|---------|
| `theorem-prefactor-consistent` | 5 = (d+1)+1 = V+1 = E−1 = κ−d | § 22b |
| `K4-is-pythagorean` | E²+κ² = 100 = 10² | § 22b |
| `K3-not-pythagorean` | K₃: E²+κ² = 45 (not perfect square) | § 22b |
| `K5-not-pythagorean` | K₅: E²+κ² = 200 (not perfect square) | § 22b |
| `theorem-total-capacity` | Information capacity = E² + κ² = 100 | § 22b |

The cosmic age formula is **fully derived**:
- **5** = spacetime + observer (5 equivalent proofs)
- **4** = V = λ (K₄ vertices = spectral gap)
- **100** = E² + κ² (K₄ uniquely Pythagorean among all K_n)

---

## Proof structure

```
FirstDistinction.agda (~8400 lines)
├── § 1-10   Foundations (distinctions, K₄ emergence)
├── § 11-15  Spectral geometry (Laplacian, eigenvalues)
├── § 16-18  Spacetime structure (3+1, signature)
├── § 19-21  Einstein equations (Ricci, coupling)
├── § 22     Predictions (α, N, Λ, τ)
│   ├── § 22f   α⁻¹ = 137.036 (spectral derivation)
│   └── § 22b   N = 5 × 4^100 (information capacity)
└── § 23     Ultimate Theorem
```

The key type:

```agda
ultimate-theorem : Unavoidable Distinction → FD-FullGR
ultimate-theorem d = full-GR-from-distinction d
```

From the unavoidability of distinction to complete 4D General Relativity.

---

## Found a bug?

Open a [GitHub Issue](https://github.com/de-johannes/FirstDistinction/issues).

If `FirstDistinction.agda` no longer compiles with the stated flags, that's a real bug. Everything else is discussion.

---

[← Back](./)
