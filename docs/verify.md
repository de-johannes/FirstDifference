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

## Proof structure

```
FirstDistinction.agda (~8000 lines)
├── § 1-10   Foundations (distinctions, K₄ emergence)
├── § 11-15  Spectral geometry (Laplacian, eigenvalues)
├── § 16-18  Spacetime structure (3+1, signature)
├── § 19-21  Einstein equations (Ricci, coupling)
├── § 22     Predictions (α, Λ, τ)
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
