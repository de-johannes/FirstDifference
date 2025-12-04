---
layout: default
title: Preface
breadcrumb: <a href="/">Home</a> &gt; Preface
---

# Preface

## The Question

Why is the universe the way it is?

Physics has been extraordinarily successful at describing *how* nature works. Newton's laws, Maxwell's equations, Einstein's relativity, quantum mechanics—each theory captures patterns in nature with stunning precision.

But each theory begins with axioms. Newton assumed three laws of motion. Einstein postulated the constancy of light speed. Quantum mechanics starts with the Schrödinger equation.

*Why these axioms?* Why not others?

This book attempts something audacious: to derive the laws of physics from *nothing but the unavoidability of distinction itself*.

---

## The Method

We use **Agda**, a dependently-typed proof assistant, with the flags `--safe` and `--without-K`. This means:

- No axioms can be postulated (everything must be constructed)
- No appeal to classical logic (everything is constructive)
- Every step is machine-verified (no human error possible)

The result is 5000+ lines of Agda code (incl. comments) that derives the Einstein field equations from pure distinction.

---

## For Whom

This book is written for:

- **Physicists** who wonder why the laws are what they are
- **Mathematicians** interested in constructive foundations
- **Computer scientists** who appreciate formal verification
- **Philosophers** seeking ontological bedrock
- **Everyone** who has asked: "Why is there something rather than nothing?"

---

## Dedication

> *This work began as an idea,*  
> *but became a dialogue—with time, with structure, with silence.*
>
> *If it carries truth, it does so not because it claims to explain,*  
> *but because it listens.*
>
> *To Lara, to Lia, to Lukas:*  
> *May you always question, and may the questions be beautiful.*
>
> *And to Julia:*  
> *For the patience to let thought unfold before it had a name.*

<p style="text-align: right;">
<em>Johannes Wielsch</em><br>
<em>December 2025</em>
</p>

---

<nav class="chapter-nav">
  <a href="abstract" class="prev">← Abstract</a>
  <a href="part-1-foundations/" class="next">Part I: Foundations →</a>
</nav>
