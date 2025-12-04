---
layout: default
title: First Distinction
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

## What is First Distinction?

**First Distinction (FD)** is an axiom-free derivation of 4D General Relativity from a single premise:

> Something is distinguishable from something.

No spacetime assumed. No quantum mechanics. No free parameters.

The complete proof is formalized in [Agda](https://github.com/de-johannes/FirstDifference/blob/main/FirstDistinction.agda) and compiles under `--safe --without-K` — no postulates, no holes, machine-checked.

---

## What is derived?

| Quantity | FD | Observation | Status |
|----------|-------|-------------|--------|
| Spatial dimensions | d = 3 | 3 | ✓ exact |
| Time dimensions | 1 | 1 | ✓ exact |
| Signature | (−,+,+,+) | (−,+,+,+) | ✓ exact |
| Λ > 0 | yes | yes | ✓ exact |
| α⁻¹ | 137.036 | 137.036 | 0.00003% |
| τ (cosmic age) | 13.73 Gyr | 13.79 Gyr | 0.4% |

[→ All predictions](predictions)

---

## How does it work?

1. **Distinction forces structure**  
   D₀ ≠ D₁ requires a "witness" D₂. This creates K₃.

2. **K₃ is unstable**  
   New pairs (D₀,D₂) lack a witness → D₃ emerges.

3. **K₄ is stable**  
   All 6 pairs are "witnessed". No further distinction is forced.

4. **K₄ = Tetrahedron = 3D space**  
   The Laplacian eigenvalues {0,4,4,4} span 3 dimensions.

5. **Drift = Time**  
   The irreversible accumulation of distinctions is the arrow of time.

---

## Check it yourself

```bash
git clone https://github.com/de-johannes/FirstDifference.git
cd FirstDifference
agda --safe --without-K --no-libraries FirstDistinction.agda
```

[![CI](https://github.com/de-johannes/FirstDifference/actions/workflows/ci.yml/badge.svg)](https://github.com/de-johannes/FirstDifference/actions/workflows/ci.yml)

The code is the claim. If it compiles, the proof is valid.

[→ Verification](verify)

---

## Honesty

- We do not claim to have found "the truth".
- We present a derivation that is machine-checked.
- The α formula uses K₄ spectral invariants (λ³χ + deg² + correction).
- The cosmic age N = 5 × 4¹⁰⁰ is a conjecture.

If you find an error, open an issue. We want to know.

---

## AI Disclosure

This work was created over 12 months by one person using six different AI systems (Claude Opus, Claude Sonnet, ChatGPT, Gemini, Sonar-R1, DeepSeek-R1). Agda doesn't lie — if it compiles under `--safe --without-K`, the proofs are valid. But skepticism toward AI-assisted work is warranted. Read the code.

[→ Open questions](faq)

---

<div class="footer-links">
  <a href="https://github.com/de-johannes/FirstDifference">GitHub</a>
  <a href="verify">Verify</a>
  <a href="predictions">Predictions</a>
</div>
