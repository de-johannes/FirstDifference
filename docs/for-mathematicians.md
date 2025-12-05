---
layout: default
title: For Mathematicians
---

# For Mathematicians

**A formal derivation in constructive type theory.**

---

## The Logical Structure

First Distinction is a theorem-proving exercise in **Agda** under strict constraints:

```
--safe        No unsafe pragmas (no trustMe, no primTrustMe)
--without-K   No uniqueness of identity proofs (compatible with HoTT)
--no-libraries   No standard library (everything from scratch)
```

This means: **every object exists only if constructed**. No axioms, no postulates, no holes.

---

## The Single Premise

We start with one type:

```agda
data Distinction : Set where
  φ  : Distinction
  ¬φ : Distinction
```

This is isomorphic to `Bool`, but with semantic intent: φ and ¬φ are the two "poles" of the first distinction D₀.

**Claim:** This premise is unavoidable.

**Proof sketch:** To deny "distinction exists," you must distinguish that denial from its opposite. The denial presupposes what it denies.

**Formalization:**

```agda
record Unavoidable (P : Set) : Set where
  field
    to-assert : P           -- To assert P requires P
    to-deny   : ¬ P → P     -- To deny P requires P

unavoidability-of-D₀ : Unavoidable Distinction
unavoidability-of-D₀ = record
  { to-assert = φ
  ; to-deny   = λ _ → φ
  }
```

---

## The Derivation Chain

From D₀, we derive:

```
D₀ (First Distinction)
 │
 ├─→ D₁ (Polarity: φ vs ¬φ)
 │
 ├─→ D₂ (Relation: D₀ ≠ D₁ witnessed)
 │    │
 │    └─→ K₃ (Complete graph on 3 vertices)
 │
 ├─→ D₃ (Forced by irreducible pair (D₀,D₂))
 │    │
 │    └─→ K₄ (Complete graph on 4 vertices) ← STABLE
 │
 ├─→ Laplacian L of K₄
 │    │
 │    ├─→ Eigenvalues {0, 4, 4, 4}
 │    │    │
 │    │    └─→ d = 3 (spatial dimension = multiplicity of λ=4)
 │    │
 │    └─→ Ricci scalar R = Tr(L) = 12
 │
 ├─→ Drift irreversibility
 │    │
 │    └─→ t = 1 (time dimension)
 │         │
 │         └─→ Signature (−,+,+,+)
 │
 └─→ Einstein equations G_μν + Λg_μν = κT_μν
      │
      ├─→ Λ = 3 (from K₄)
      └─→ κ = 8 (from Bool × K₄)
```

Every arrow is a **theorem with a `refl` proof** (computed, not asserted).

---

## Key Constructions

### The K₄ Graph

```agda
data K4Vertex : Set where
  v₀ v₁ v₂ v₃ : K4Vertex

data K4Edge : K4Vertex → K4Vertex → Set where
  -- All 6 edges (complete graph)
  e₀₁ : K4Edge v₀ v₁
  e₀₂ : K4Edge v₀ v₂
  e₀₃ : K4Edge v₀ v₃
  e₁₂ : K4Edge v₁ v₂
  e₁₃ : K4Edge v₁ v₃
  e₂₃ : K4Edge v₂ v₃
```

### The Laplacian

```agda
-- L = D - A where D = degree matrix, A = adjacency
-- For K₄: L = 4I - J where J is all-ones
-- Eigenvalues: 0 (once), 4 (three times)

laplacianK4 : K4Vertex → K4Vertex → ℤ
laplacianK4 v w with v ≟ w
... | yes _ = mkℤ 3 0   -- Diagonal: degree = 3
... | no  _ = mkℤ 0 1   -- Off-diagonal: -1 (using ℤ representation)
```

### The Eigenvector Proof

```agda
-- Eigenvector e₁ = (1, -1, 0, 0) with eigenvalue 4
theorem-eigenvector-1 : L · e₁ ≡ 4 · e₁
theorem-eigenvector-1 = refl  -- COMPUTED!
```

---

## The Integer Construction

We build ℤ as a **setoid quotient**:

```agda
record ℤ : Set where
  constructor mkℤ
  field
    pos : ℕ
    neg : ℕ

-- Equivalence: (a,b) ≃ (c,d) iff a+d = c+b
_≃ℤ_ : ℤ → ℤ → Set
mkℤ a b ≃ℤ mkℤ c d = (a + d) ≡ (c + b)
```

This is process-based: integers are **signed winding numbers** on the drift graph.

---

## The Memory Function

```agda
-- Memory = pairs of distinctions = triangular numbers
triangular : ℕ → ℕ
triangular zero = zero
triangular (suc n) = n + triangular n

memory : ℕ → ℕ
memory = triangular

-- K₄ has 6 edges = C(4,2) = 4×3/2
theorem-K4-edges : memory 4 ≡ 6
theorem-K4-edges = refl
```

---

## The Captures Relation

The key to K₄ stability: **all pairs are captured**.

```agda
-- A pair is captured if:
-- 1. Reflexive: (Dᵢ, Dᵢ) is captured by Dᵢ itself
-- 2. Defining: (D₀, D₁) is captured by D₂ (its definition)
--              (D₀, D₂) is captured by D₃
--              (D₁, D₂) is captured by D₃

captures? : GenesisPair → Bool
captures? p = is-reflexive-pair p ∨ is-defining-pair p

-- All K₄ pairs are captured
theorem-K4-stable : (p : GenesisPair) → captures? p ≡ true ∨ ...
```

---

## The α Formula

Two independent derivations produce the same number:

### Spectral Derivation

$$\alpha^{-1} = \lambda^3 \chi + \deg^2 + \frac{V}{\deg(E^2+1)}$$

```agda
alpha-inverse-integer : ℕ
alpha-inverse-integer = (λ-nat ^ 3) * χ + (deg * deg)
-- = 64 × 2 + 9 = 137

theorem-alpha-integer : alpha-inverse-integer ≡ 137
theorem-alpha-integer = refl  -- COMPUTED!
```

### Operad Derivation

$$\alpha^{-1} = \Pi(\text{categorical arities}) \times \chi + \Sigma(\text{algebraic arities})$$

```agda
-- Categorical: 2 × 4 × 2 × 4 = 64 (PRODUCT - divergent)
-- Algebraic: 3 + 3 + 2 + 1 = 9 (SUM - convergent)

alpha-from-operad : ℕ
alpha-from-operad = (2 * 4 * 2 * 4) * 2 + (3 + 3 + 2 + 1)
-- = 64 × 2 + 9 = 137

theorem-operad-equals-spectral : alpha-from-operad ≡ alpha-integer
theorem-operad-equals-spectral = refl
```

**Epistemological note:** The formulas computing 137 are **theorems** (Agda-verified). That this number IS the physical fine structure constant α⁻¹ is **hypothesis**, supported by the 0.00003% agreement.

---

## Proof Statistics

| Metric | Value |
|--------|-------|
| Total lines | ~10,000 |
| Sections (§) | 25+ |
| Theorems with `refl` | 100+ |
| Postulates | **0** |
| Holes | **0** |
| Axiom K uses | **0** |

## What IS Proven vs What is Hypothesis

### PROVEN (Agda --safe --without-K):
- K₄ emerges as the unique stable graph under the captures relation
- The formulas compute specific numbers: d=3, 137.036, N=5×4¹⁰⁰, etc.
- All mathematical derivations are machine-verified

### HYPOTHESIS (not checkable by Agda):
- That K₄ structure IS physical spacetime
- That 137.036 IS α⁻¹ (rather than numerical coincidence)
- That N × t_Planck IS the cosmic age
- Any claim about "physics" beyond the mathematical computation

**The mathematics is proven. The physics correspondence is testable hypothesis supported by remarkable numerical agreement.**

---

## What's Already Proven (Mathematics)

| Result | Status | Where |
|--------|--------|-------|
| K₄ uniqueness | ✅ PROVEN | FirstDistinction.agda § 7 + K4Uniqueness.agda |
| Correction term 4/111 | ✅ PROVEN | FirstDistinction.agda § 22f.3 |
| Operad arities forced | ✅ PROVEN | FirstDistinction.agda § 22f.0a |
| Time direction / signature | ✅ PROVEN | FirstDistinction.agda § 13 (`theorem-temporal-signature = refl`) |
| Formula result = 137.036 | ✅ PROVEN | FirstDistinction.agda § 22f |
| N = 5 × 4¹⁰⁰ | ✅ PROVEN | FirstDistinction.agda § 22b'' |

**Note:** "Proven" means the mathematical computation is verified. The identification with physics (e.g., "137.036 IS α⁻¹") remains hypothesis.

**Further research may include**:
- Deriving Hilbert space / quantum mechanics from distinction
- Higher-order corrections to α beyond 4/111

---

## Verify It Yourself

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K --no-libraries FirstDistinction.agda
```

Compilation = validity. No interpretation needed.

---

## The Agda Source

The complete proof: [FirstDistinction.agda](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.agda)

Key sections:
- § 1-4: Type theory foundations
- § 5-7: Distinction and K₄ emergence
- § 10-12: Laplacian and eigenvalues
- § 14-18: Einstein equations
- § 22: Predictions (α, Λ, τ)

---

<div class="footer-links">
  <a href="/">← Home</a>
  <a href="for-physicists">← For Physicists</a>
</div>
