# Free Entropy & Quantum Minimum Description Length — Wiki Index

> **Project:** "Free entropy and quantum minimum description length"
> **Authors:** Patrick Hayden, Alexander Maloney, Jinzhao Wang, Yuxiang Yang
> **Last updated:** 2026-04-08

**[[intro|Start here]]** -- overview of the project, main result, and how to navigate.

---

## Source Papers

| File | Title | Role |
|------|-------|------|
| [[Letter]] (`sources/letter.tex`) | Free entropy and quantum minimum description length | PRL letter (announcement) |
| [[Article]] (`sources/article.tex`) | Quantum minimum description of density matrices | Full journal paper (proofs) |
| [[Notes]] (`sources/Free.tex`) | Free entropy and quantum minimum description length | Extended notes (+ unitary & observable programming) |

---

## Core Concepts

### Free Entropy & Information Theory
- [[concepts/free-entropy-intro|Introduction to Free Entropy]] — self-contained pedagogical introduction
- [[concepts/free-entropy|Free Entropy]] — Voiculescu's non-commutative Shannon entropy
- [[concepts/physical-free-entropy|Physical Free Entropy]] — finite-dimensional, resolution-dependent version
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] — leading-order scaling coefficient
- [[definitions/regularized-free-entropy|Regularized Free Entropy]] — the $O(1)$ eigenvalue-dependent correction
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] — the compression task and main result
- [[concepts/schumacher-compression|Schumacher Compression]] — contrasting: von Neumann entropy governs this
- [[concepts/covering-numbers|Covering Numbers]] — Kolmogorov $\varepsilon$-entropy underlying physical free entropy

### Free Probability
- [[concepts/free-probability-basics|Introduction to Free Probability]] — self-contained pedagogical introduction
- [[concepts/free-probability-theory|Free Probability Theory]] — the broader mathematical framework
- [[concepts/semicircular-element|Semicircular Element and Free Independence]] — non-commutative Gaussian and freeness
- [[concepts/vandermonde-determinant|Vandermonde Determinant]] — eigenvalue repulsion factor

### Representation Theory
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] — the fundamental decomposition
- [[concepts/schur-transform|Schur Transform]] — the unitary implementing it
- [[concepts/young-diagrams|Young Diagrams and Partitions]] — labels for irreps
- [[concepts/schur-polynomials|Schur Polynomials]] — characters of GL(d) representations
- [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin Basis]] — canonical basis for GL(d) irreps
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] — dimension of irreps
- [[concepts/prv-component|PRV Component]] — Parthasarathy-Ranga Rao-Varadarajan component
- [[concepts/kumars-theorem|Kumar's Theorem]] — multiplicity-one for PRV components
- [[concepts/casimir-operator|Casimir Operator]] — used in perturbation analysis
- [[concepts/kostant-partition-function|Kostant Partition Function]] — bounds weight multiplicities
- [[concepts/flag-manifold|Flag Manifold]] — the eigenbasis manifold

### Cloning & Compression
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] — the key technical innovation
- [[concepts/werners-cloning-map|Werner's Cloning Map]] — the qubit special case
- [[concepts/ych-scheme|YCH Scheme]] — Yang-Chiribella-Hayashi precursor
- [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]] — for the converse proof
- [[concepts/petz-recovery-map|Petz Recovery Map]] — reverse cloner interpretation
- [[concepts/holevo-information|Holevo Information]] — used in converse proofs

### Geometric Quantization
- [[concepts/kks-theorem|KKS Theorem]] — explains the factor of 1/2 between free entropy and QMDL

---

## Formal Definitions

| Definition | File |
|------------|------|
| [[definitions/compression-code|Compression Code]] | $(|M|, \delta)$-code |
| [[definitions/generalized-cloning-map-def|Generalized Cloning Map (Formal)]] | Stinespring & Choi forms |
| [[definitions/free-entropy-voiculescu|Free Entropy (Voiculescu)]] | Microstate definition |
| [[definitions/physical-free-entropy-def|Physical Free Entropy (Formal)]] | Covering number definition |
| [[definitions/regularized-free-entropy|Regularized Free Entropy]] | $\chi_{\mathrm{reg}}(\rho)$ |
| [[definitions/free-entropy-dimension-def|Free Entropy Dimension (Formal)]] | $\delta(a)$ |
| [[definitions/covariant-channel|U(d)-Covariant Channel]] | Symmetry requirement |
| [[definitions/scaling-regime|Scaling Regime]] | Asymptotic regime for cloning fidelity |
| [[definitions/typical-set|Typical Set]] | $T_{p,n}$ |
| [[definitions/edge-gap|Edge Gap]] | $g_\lambda$ |
| [[definitions/normalized-gl-irrep|Normalized GL Irrep State]] | $\rho_\lambda$ |
| [[definitions/kostka-number|Kostka Number]] | $K_{\lambda, w}$ |
| [[definitions/weight-space|Weight and Weight Space]] | Weight decomposition |
| [[definitions/distance-between-irreps|Distance Between Irreps]] | $d(\mu, \nu)$ |

---

## Main Results

| Result | Type | Source |
|--------|------|--------|
| [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] | Theorem | Article, Notes |
| [[results/achievability|Achievability (State Compression)]] | Theorem | Article (Thm 2), Notes |
| [[results/converse|Converse (State Compression)]] | Theorem | Article (Thm 3), Notes |

---

## Supporting Propositions

| Result | Type | Source |
|--------|------|--------|
| [[results/propositions/choi-matrix-lemma|Choi Matrix Lemma (Prop 1)]] | Proposition | Article |
| [[results/propositions/reverse-cloner|Reverse Cloner (Prop 2)]] | Proposition | Article |
| [[results/propositions/commutativity|Commutativity (Prop 3)]] | Proposition | Article |
| [[results/propositions/orbit-sector-compression|Orbit Sector Compression (Prop 4)]] | Proposition | Article |

## Supporting Lemmas

| Result | Type | Source |
|--------|------|--------|
| [[results/lemmas/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] | Lemma | Article |
| [[results/lemmas/principal-angles|Principal Angles (Lemma 4)]] | Lemma | Article |
| [[results/lemmas/monotonicity-lemma|Monotonicity (Lemma 5)]] | Lemma | Article |
| [[results/lemmas/davis-kahan|Davis-Kahan Theorem (Lemma 6)]] | Lemma | Article |
| [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]] | Lemma | Article |
| [[results/lemmas/tail-mass|Tail Mass (Lemma 8)]] | Lemma | Article |
| [[results/lemmas/probability-ratio|Probability Ratio (Lemma 9)]] | Lemma | Article |
| [[results/lemmas/dimension-ratio|Dimension Ratio (Lemma 10)]] | Lemma | Article |
| [[results/lemmas/weyl-dimension-asymptotic|Asymptotic Weyl Dimension (Lemma 11)]] | Lemma | Article |
| [[results/lemmas/sanov-theorem|Sanov's Theorem (Lemma 12)]] | Lemma | Article |

---

## Dependency Graph (Proof Architecture)

```
                    QMDL = Free Entropy
                   /                    \
        Achievability (Thm 2)      Converse (Thm 3)
              |                         |
    Cloning Fidelity (Thm 1)    Orbit Sector (Prop 4)
     /     |      |      \              |
  Lem 7  Lem 9  Lem 8  Lem 10   Weyl Dimension (Lem 11)
    |      |                          |
  Lem 6  Lem 3                   Sanov (Lem 12)
 (D-K)  (Kostka)
    |      |
  Casimir  GT Basis
```

---

## Notation

- [[notation|Notation Glossary]] — all symbols used across the papers

---

## Open Questions

- [[open-questions/cloning-optimality|Open: Optimality of the Generalized Cloning Map]] — is the PRV channel the fidelity maximizer among all covariant channels?
- [[open-questions/degenerate-spectrum|Open: QMDL for Degenerate Spectrum]] — extend the main result to density matrices with repeated eigenvalues
- [[open-questions/error-scaling|Open: Error Scaling]] — optimal error exponent for qudit compression
- [[open-questions/free-entropy-conjecture|Conjecture: Free Entropy as Universal QMDL]] — extends to all operators?
- [[open-questions/programming-extensions|Open: Programming Extensions (Notes)]] — unitary programming, observable programming, state programming, and associated open problems

---

## References

- [[references/key-references|Key References]] — annotated bibliography of key cited works

---

## How to Use This Wiki

1. **Open in Obsidian**: point Obsidian at `~/Documents/free-entropy-wiki/`. All `[[wikilinks]]` will be clickable.
2. **Ask questions**: run Claude Code in this directory and ask anything about the papers.
3. **Update after paper changes**: export new `.tex` from Overleaf, drop in `sources/`, then ask Claude to diff and update.
4. **Lint**: periodically ask Claude to check for contradictions, stale pages, or missing links.
