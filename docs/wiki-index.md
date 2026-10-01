# Free Entropy & Quantum Minimum Description Length — Wiki Index

> **Project:** "Free entropy and quantum minimum description length"
> **Authors:** Patrick Hayden, Alexander Maloney, Jinzhao Wang, Yuxiang Yang
> **Last updated:** 2026-10-01

**[[intro|Start here]]** -- overview of the project, main result, and how to navigate.

**[[proof-structure|Current proof structure]]** -- how representation theory, finite cloning bounds,
physical compression and the quantitative converse fit together.

**[[formalization|Lean formalization and reproduction]]** -- checked scope and commands
for Lean, Comparator and Nanoda.

---

## Source Papers

| File | Title | Role |
|------|-------|------|
| [[Letter]] (repository-root `letter.tex`) | Free entropy and quantum minimum description length | Current Letter: physical entropy, orbit geometry and operational relation |
| [[Article]] (repository-root `article.tex`) | Quantum minimum description of density matrices | Full journal paper (proofs) |
| [[Notes]] (`sources/Free.tex`, historical local snapshot) | Free entropy and quantum minimum description length | Earlier extended notes (+ unitary & observable programming) |

The repository-root Article and Letter match the author-supplied sources.
They share `free.bib`; the Letter also includes `compression.pdf`.
The [companion source map](https://github.com/JWang226/QMDL/blob/main/metadata/letter-source-map.json)
records file hashes, Letter equation labels and the boundary of Lean coverage.

---

## Core Concepts

### Free Probability & Free Entropy
- [[concepts/free-probability-and-entropy|Introduction to Free Probability, Free Entropy, and Free Entropy Dimension]] — self-contained pedagogical introduction
- [[concepts/free-probability-theory|Free Probability Theory]] — the broader mathematical framework
- [[concepts/semicircular-element|Semicircular Element and Free Independence]] — non-commutative Gaussian and freeness
- [[concepts/free-entropy|Free Entropy]] — Voiculescu's non-commutative Shannon entropy
- [[concepts/physical-free-entropy|Physical Free Entropy]] — finite-dimensional, resolution-dependent version
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] — leading-order scaling coefficient
- [[definitions/regularized-free-entropy|Regularized Free Entropy]] — the $O(1)$ eigenvalue-dependent correction
- [[concepts/vandermonde-determinant|Vandermonde Determinant]] — eigenvalue repulsion factor

### Information Theory & Compression
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] — the compression task and main result
- [[concepts/kolmogorov-complexity|Kolmogorov Complexity & QKC]] — classical and quantum descriptive complexity
- [[concepts/schumacher-compression|Schumacher Compression]] — contrasting: von Neumann entropy governs this
- [[concepts/covering-numbers|Covering Numbers]] — comparison with physical entropy up to an additive $O(1)$

### Representation Theory
- [[concepts/schur-weyl-duality|Schur-Weyl Duality & Schur Transform]] — the fundamental decomposition and its unitary implementation
- [[concepts/young-diagrams|Young Diagrams and Partitions]] — labels for irreps
- [[concepts/schur-polynomials|Schur Polynomials]] — characters of GL(d) representations
- [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin Basis]] — canonical basis for GL(d) irreps
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] — dimension of irreps
- [[concepts/prv-component|PRV Component]] — channel component and its relation to the Cartan construction
- [[concepts/kumars-theorem|Kumar's Theorem]] — general background and the multiplicity-one case needed here
- [[concepts/casimir-operator|Casimir Operator]] — used in perturbation analysis
- [[concepts/kostant-partition-function|Kostant Partition Function]] — bounds weight multiplicities
- [[concepts/flag-manifold|Flag Manifold]] — the eigenbasis manifold

### Cloning & Compression
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] — the key technical innovation
- [[concepts/werners-cloning-map|Werner's Cloning Map]] — the qubit special case
- [[concepts/ych-scheme|YCH Scheme]] — Yang-Chiribella-Hayashi precursor
- [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]] — exact incompressibility and the quantitative converse
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
| [[definitions/physical-free-entropy-def|Physical Free Entropy (Definition)]] | Ambient Hilbert–Schmidt tube-volume ratio |
| [[definitions/regularized-free-entropy|Regularized Free Entropy]] | $\chi_{\mathrm{reg}}(\rho)$ |
| [[definitions/free-entropy-dimension-def|Free Entropy Dimension (Formal)]] | $\delta(a)$ |
| [[definitions/covariant-channel|U(d)-Covariant Channel]] | Symmetry requirement |
| [[definitions/scaling-regime|Scaling Regime]] | Asymptotic regime for vanishing cloning error |
| [[definitions/typical-set|Typical Set]] | $T_{p,n}$ |
| [[definitions/edge-gap|Edge Gap]] | $g_\lambda$ |
| [[definitions/normalized-gl-irrep|Normalized GL Irrep State]] | $\rho_\lambda$ |
| [[definitions/kostka-number|Kostka Number]] | $K_{\lambda, w}$ |
| [[definitions/weight-space|Weight and Weight Space]] | Weight decomposition |
| [[definitions/distance-between-irreps|Distance Between Irreps]] | $d(\mu, \nu)$ |

---

## Current Article results

Theorem numbers below refer to the bundled Article. The current [[Letter]]
states its compression results as labeled equations and its double-scaling
bridge as a remark; [[Notes]] retains historical numbering. Always qualify
shared equation labels by their source document.

| Result | Article label | Formal role |
| --- | --- | --- |
| [[results/achievability|Theorem 1: achievability]] | `thm:qmdl`, `thm:achievability` | Exact memory constant and uniform $O(\log n/\sqrt n)$ error. |
| [[results/converse|Theorem 1: converse]] | `thm:qmdl`, `thm:converse` | Haar-average lower bound for arbitrary physical codes. |
| [[results/cloning-fidelity|Theorem 2: cloning accuracy]] | `thm:main` | Finite trace-distance bounds for the original Choi channels. |

## Supporting propositions

| Result | Article label | Role |
| --- | --- | --- |
| [[results/propositions/choi-matrix-lemma|Cartan and Choi formulas]] | `prop:choi` | Identify the constructed forward channel with the source formula. |
| [[results/propositions/reverse-cloner|Reverse cloner and Petz map]] | `prop:reverse` | Identify the reverse channel and recovery expression. |
| [[results/propositions/commutativity|Commutativity]] | `prop:commutativity` | Paper-level structural result; see the page for its formalization boundary. |
| [[results/propositions/orbit-sector-compression|Haar-orbit memory bound]] | `prop:compact_orbit_memory` | Quantitative finite memory lower bound used in the converse. |

## Supporting estimates

| Explanation | Article label or status | Role in the current proof |
| --- | --- | --- |
| [[results/lemmas/kostka-monotonicity|Multiplicity monotonicity]] | `lem:kostka` | Compare the relevant weight multiplicities. |
| [[results/lemmas/perturbation-lemma|Highest-weight projector deficit]] | `lem:perturbation` | Control the traced loss using a Casimir gap. |
| [[results/lemmas/tail-mass|Uniform mean depth]] | `lem:tail` | Average finite deficits without an $n$-dependent truncation. |
| [[results/lemmas/probability-ratio|Eigenvalue ratio]] | `lem:ratio` | Control normalized weight-state coefficients. |
| [[results/lemmas/dimension-ratio|Weyl dimension ratio]] | `lem:dim_ratio` | Bound the finite normalization loss. |
| [[results/lemmas/weyl-dimension-asymptotic|Asymptotic Weyl dimension]] | `lem:weyl_asymptotic` | Retain the additive memory constant. |
| [[results/lemmas/sanov-theorem|Physical sector concentration]] | `lem:tail_prob` | Bound the mass outside the typical window. |
| [[results/lemmas/monotonicity-lemma|Positive-order trace comparison]] | Supporting inequality | Pass from a positive channel branch to a trace-distance bound. |

[[results/lemmas/principal-angles|Principal angles]] and
[[results/lemmas/davis-kahan|Davis–Kahan perturbation theory]] are retained as
background to the older fidelity-based presentation. The current finite
trace-distance route is described in [[proof-structure]].

## Proof reading route

1. [[proof-structure|Start with the dependency diagram and module map]].
2. Read [[results/cloning-fidelity|the finite cloning estimate]] and its Cartan/Choi/Petz identifications.
3. Follow [[results/achievability|typical-sector compression to a padded target]].
4. Follow [[results/converse|the spectral-gap and Haar-average converse]].
5. Use [[formalization|the verification guide]] to check the exact formal statements.

---

## Notation

- [[notation|Notation Glossary]] — all symbols used across the papers

---

## Open Questions

- [[open-questions/cloning-optimality|Open: Optimality of the Generalized Cloning Map]] — is the PRV channel the fidelity maximizer among all covariant channels?
- [[open-questions/degenerate-spectrum|Open: QMDL for Degenerate Spectrum]] — extend the main result to repeated positive eigenvalues; repeated zeros are already covered
- [[open-questions/error-scaling|Open: Error Scaling]] — optimal tradeoffs beyond the proved $O(\log n/\sqrt n)$ rate
- [[open-questions/free-entropy-conjecture|Conjecture: Free Entropy as Universal QMDL & Programming Extensions]] — broader operators in settings where free entropy is defined, including unitary/observable/state programming questions

---

## References

- [[references/key-references|Key References]] — annotated bibliography of key cited works

---

## How to use this wiki

Browse the published site or open the repository's `docs/` folder as an
Obsidian vault. The current Article source and Lean library are linked from
the result pages. When sources change, reconcile statement labels, proof
routes and the [[notation|notation glossary]], then record the update in
[[log|the change log]].
