# The Irrefutable First Difference — Agda Core

This repo exposes a **safe, axiom-free core** of the program:

- `Core/TokenPrinciple.agda`: a tiny interface that captures the Token Principle.
- `Core/Irrefutable.agda`: machine-checked irrefutability of `D₀` **relative to** the Token Principle.
- `Core/Demo.agda`: a trivial concrete instance (compiles under `--safe`, no postulates).
- `Structures/CutCat.agda`: a thin category on `ℕ` and a toy “ledger cut” embedding.
- `Structures/Drift.agda`: a minimal, runnable drift toy (boolean, finite, decidable).
- `Examples/DriftSim.agda`: small examples that normalise during type-checking.

What’s **not** here (yet): the full sequent-calculus formalisation and the HoTT correspondence.  
See the OSF project for the complete proof PDF and roadmap.

## Build

```bash
agda --safe --without-K -i src src/All.agda
