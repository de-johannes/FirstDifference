---
layout: default
title: D₀ (Home)
---

<div class="hero">
  <div class="k4-symbol">
    <svg viewBox="0 0 100 100" class="tetrahedron">
      <g stroke="currentColor" stroke-width="1.5" fill="none">
        <!-- Tetrahedron edges -->
        <line x1="50" y1="15" x2="20" y2="75"/>
        <line x1="50" y1="15" x2="80" y2="75"/>
        <line x1="50" y1="15" x2="50" y2="55"/>
        <line x1="20" y1="75" x2="80" y2="75"/>
        <line x1="20" y1="75" x2="50" y2="55"/>
        <line x1="80" y1="75" x2="50" y2="55"/>
        <!-- Vertices -->
        <circle cx="50" cy="15" r="3" fill="currentColor"/>
        <circle cx="20" cy="75" r="3" fill="currentColor"/>
        <circle cx="80" cy="75" r="3" fill="currentColor"/>
        <circle cx="50" cy="55" r="3" fill="currentColor"/>
      </g>
    </svg>
  </div>
  <p class="tagline">4 vertices. 6 edges. Everything else follows.</p>
</div>

---

## The Challenge

**Try to deny that distinction exists.**

To say "there is no distinction" — you must distinguish that statement from its opposite. To think "nothing is different from anything" — you must differentiate that thought from other thoughts.

**You cannot deny distinction without using distinction.**

This is not wordplay. It's an unavoidable logical fact:
- To assert requires distinguishing assertion from non-assertion
- To deny requires distinguishing denial from acceptance  
- Even silence distinguishes itself from speech

The First Distinction (D₀) cannot be coherently rejected. It is **self-evident** in the strongest possible sense: its denial presupposes it.

---

## The Ontology

From this single unavoidable fact, we derive everything:

> **What exists is exactly what can be constructed.**

This is not a philosophical position we *choose*. It's the position that Agda (our proof system) *embodies*. In constructive type theory:
- "X exists" means "X can be built"
- No axioms, no assumptions, no faith required
- If you can't construct it, it doesn't exist in the proof

**One premise. Zero parameters. Machine-checked.**

---

## How deep do you want to go?

| Level | For whom | Start here |
|-------|----------|------------|
| **1. Curious** | "What's the claim?" | Keep reading below |
| **2. Skeptical** | "Prove it compiles" | [→ Verification](verify) |
| **3. Technical** | "Show me the math" | [→ Part 1: Foundations](part-1-foundations/) |
| **4. Expert** | "I want the Agda" | [→ FirstDistinction.agda](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.agda) |

---

## What is First Distinction?

**First Distinction (FD)** is an axiom-free derivation of 4D General Relativity from a single premise:

> Something is distinguishable from something.

No spacetime assumed. No quantum mechanics. No free parameters.

The complete proof is formalized in [Agda](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.agda) and compiles under `--safe --without-K` — no postulates, no holes, machine-checked.

---

## What is Agda?

**Agda** is a functional programming language with dependent types and an interactive proof assistant. Unlike mathematical proofs on paper, every step is machine-checked — the compiler guarantees logical consistency.

**Why Agda for First Distinction?**

- **No hidden assumptions:** The `--safe --without-K` mode forbids logical axioms and postulates. What is not explicitly derived does not exist.
- **Full transparency:** Anyone can verify the proof themselves — a single compiler run suffices.
- **Reproducible:** The result does not depend on human interpretation.

**What does "proof" mean in Agda?**

A proof is a program whose type encodes a mathematical statement. If the program compiles, the statement is proven.

- *For physicists:* Like a numerical experiment that is always exactly reproducible — but with symbolic rather than numerical precision.
- *For mathematicians:* Like a formally verified proof in a Hilbert system, machine-checked for correctness.

---

## What is derived?

| Quantity | FD | Observation | Status |
|----------|-------|-------------|--------|
| Spatial dimensions | d = 3 | 3 | ✓ exact |
| Time dimensions | 1 | 1 | ✓ exact |
| Signature | (−,+,+,+) | (−,+,+,+) | ✓ exact |
| Λ > 0 | yes | yes | ✓ exact |
| α⁻¹ | 137.036 | 137.036 | 0.00003% |
| N (Planck times) | 5×4¹⁰⁰ | ~10⁶¹ | ✓ derived |
| τ (cosmic age) | 13.73 Gyr | 13.79 Gyr | 0.4% |

[→ All predictions](predictions)

---

## Why Type Theory?

In 1972, Per Martin-Löf created intuitionistic type theory. He didn't know he was formalizing physics.

The unit type ⊤ has exactly one inhabitant. The empty type ⊥ has none. This isn't arbitrary — it's the **only** way to have "something" versus "nothing" without presupposing structure.

We now recognize: **⊤ with `tt` IS D₀ with φ.** Same structure, different notation.

| Martin-Löf (1972) | First Distinction |
|-------------------|-------------------|
| ⊥ (empty type) | Before distinction |
| ⊤ (unit type) | D₀ — the First Distinction |
| Bool | φ vs ¬φ |
| _≡_ (identity) | Self-recognition of D₀ |

Type theory works because distinction is unavoidable. Martin-Löf formalized the consequence; we derive the cause.

---

## How does it work?

**In plain language:**

1. **You can't have ONE distinction alone**  
   If D₀ exists, you can distinguish D₀ from "not D₀". That's a second distinction D₁.

2. **Two distinctions need a third**  
   "D₀ is different from D₁" — that *relation* is itself a distinction: D₂.

3. **Three isn't stable**  
   Now (D₀, D₂) is a new pair without a witness. This forces D₃.

4. **Four is stable**  
   With 4 distinctions, all 6 possible pairs are "witnessed". Nothing new is forced.

5. **Four points = Tetrahedron = 3D space**  
   The geometry of 4 vertices connected by 6 edges IS three-dimensional space.

6. **The process of arriving there = Time**  
   The irreversible sequence D₀ → D₁ → D₂ → D₃ is the arrow of time.

**That's it.** From "distinction exists" to 3+1 dimensional spacetime in 6 steps.

---

## Check it yourself

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K --no-libraries FirstDistinction.agda
```

[![CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml)

The code is the claim. If it compiles, the proof is valid.

[→ Verification](verify)

---

## Honesty

- We do not claim to have found "the truth".
- We present a derivation that is machine-checked.
- The α formula uses K₄ spectral invariants (λ³χ + deg² + correction).
- The cosmic age N = 5 × 4¹⁰⁰ is now fully derived from K₄ (see § 22b'').

If you find an error, open an issue. We want to know.

---

## AI Disclosure

This work was created over 12 months by one person using six different AI systems (Claude Opus, Claude Sonnet, ChatGPT, Gemini, Sonar-R1, DeepSeek-R1). Agda doesn't lie — if it compiles under `--safe --without-K`, the proof is valid.

[→ Open questions](faq)

---

<div class="footer-links">
  <a href="https://github.com/de-johannes/FirstDistinction">GitHub</a>
  <a href="verify">Verify</a>
  <a href="predictions">Predictions</a>
</div>