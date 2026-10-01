# Normalized GL Irrep State

**Source:** Article, Notes (used throughout)

## Statement

For a density matrix $\rho$ with eigenvalues $x_1, \ldots, x_d$ and a partition $\lambda$, the **normalized GL irrep state** is:

$$\rho_\lambda = \frac{\pi_\lambda(\rho)}{s_\lambda(x)}$$

Here $\pi_\lambda$ is the polynomial representation extended to matrices, and $s_\lambda(x)=\operatorname{Tr}\pi_\lambda(\rho)$. The normalization requires $s_\lambda(x)>0$. For a rank-$r$ source this holds for the supported partitions with at most $r$ rows; unsupported sectors have zero probability and need no normalized conditional state.

## Intuition

After the [[concepts/schur-weyl-duality|Schur transform]], the state $\rho^{\otimes n}$ decomposes into sectors. In sector $\lambda$, the GL part is $\rho_\lambda$ -- this is the "shape" of the state in that representation. The $S_n$ part is always maximally mixed and carries no information about the eigenbasis.

## Weight Decomposition (Block-Diagonal Structure)

$\rho_\lambda$ is **block-diagonal** in the [[definitions/weight-space|Weight Space]] decomposition. Each weight $w = \lambda - \delta$ (where $\delta \in Q_+$ is the weight offset from the highest weight) gives a block:

$$\rho_\lambda = \sum_{\delta \in Q_+} \frac{x^{\lambda - \delta}}{s_\lambda(x)} \cdot \Pi_{\lambda - \delta}$$

where $\Pi_{\lambda-\delta}$ is the projector onto the weight-$(\lambda - \delta)$ subspace, which has dimension $K_{\lambda, \lambda - \delta}$ (the [[definitions/kostka-number|Kostka Number]]).

The eigenvalue of $\rho_\lambda$ on the weight-$(\lambda - \delta)$ block is $x^{\lambda - \delta}/s_\lambda(x)$, where $x^w = x_1^{w_1} \cdots x_d^{w_d}$ is the monomial. This is the eigenvalue on each vector in that weight space. The probability of the whole block is $m_\lambda(\delta)x^{\lambda-\delta}/s_\lambda(x)$; the multiplicity factor is essential.

**Key point:** in an eigenbasis of the source, $\rho_\lambda$ is scalar on each weight space, hence diagonal in **every** orthonormal weight basis, including the [[concepts/gelfand-tsetlin-basis|GT basis]]. On the full unitary orbit it is conjugated by the representation action. The block structure permits the weight-by-weight trace-deficit analysis in [[results/cloning-fidelity|Article Theorem 2]].

## Qubit Example ($d = 2$)

For a qubit ($d = 2$) with eigenvalues $x_1 = p$, $x_2 = 1-p$, the irrep $\lambda = (n/2 + J, n/2 - J)$ has dimension $2J + 1$. The weights are $w_k = (n/2 + J - k,\, n/2 - J + k)$ for $k = 0, 1, \ldots, 2J$.

Each weight space is **1-dimensional** (all Kostka numbers are 1 for $d = 2$), so $\rho_\lambda$ is fully diagonal:

$$\rho_\lambda = \sum_{k=0}^{2J} \frac{p^{n/2+J-k}(1-p)^{n/2-J+k}}{s_\lambda(p, 1-p)} |k\rangle\langle k|$$

The Schur polynomial is $s_\lambda(p, 1-p) = \sum_{k=0}^{2J} p^{n/2+J-k}(1-p)^{n/2-J+k}$, which is a finite geometric sum. The eigenvalues decay geometrically from the highest weight ($k = 0$, eigenvalue $\propto p^{n/2+J}(1-p)^{n/2-J}$) to the lowest weight ($k = 2J$, eigenvalue $\propto p^{n/2-J}(1-p)^{n/2+J}$). For $p > 1/2$, most of the spectral mass concentrates near $k = 0$ (the highest weight).

## Connection to Proof Architecture

The encoder maps the normalized state to the padded target, and the decoder uses the reverse cloner. The current proof retains a highest-weight Kraus branch, estimates its positive trace loss in each weight block using the localized Casimir gap, and averages those losses using the coefficient-ratio and mean-depth estimates. This yields trace distance directly. It does not require an additional fidelity-to-trace-distance square root.

## Formal Identification

`canonicalMonomialState_eq_relativeState` in `CanonicalMonomialState.lean` proves that the normalized monomial diagonal is the relative-weight state used by the cloning proof, including zero eigenvalues for supported rows. `canonicalOrbitState` conjugates it by the actual canonical unitary representation. This identity connects the physical tensor source to the canonical theorem; it is not a supplied state-identification premise. See [[proof-structure]].

## Used By

- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]]
- [[results/achievability|Achievability (State Compression)]]

## External References

- [Goodman and Wallach, *Symmetry, Representations, and Invariants* (Springer, 2009)](https://doi.org/10.1007/978-0-387-79852-3)
- [Irreducible representation (Wikipedia)](https://en.wikipedia.org/wiki/Irreducible_representation)
