# Normalized GL Irrep State

**Source:** Article, Notes (used throughout)

## Statement

For a density matrix $\rho$ with eigenvalues $x_1, \ldots, x_d$ and a partition $\lambda$, the **normalized GL irrep state** is:

$$\rho_\lambda = \frac{\pi_\lambda(\rho)}{s_\lambda(x)}$$

where $\pi_\lambda(\rho) = \sum_\sigma \rho^{\otimes n} \cdot P_\sigma$ restricted to $H_\lambda$ (the GL irrep component), and $s_\lambda(x)$ is the [[concepts/schur-polynomials|Schur polynomial]] ensuring $\mathrm{Tr}[\rho_\lambda] = 1$.

## Intuition

After the [[concepts/schur-weyl-duality|Schur transform]], the state $\rho^{\otimes n}$ decomposes into sectors. In sector $\lambda$, the GL part is $\rho_\lambda$ -- this is the "shape" of the state in that representation. The $S_n$ part is always maximally mixed and carries no information about the eigenbasis.

## Weight Decomposition (Block-Diagonal Structure)

$\rho_\lambda$ is **block-diagonal** in the [[definitions/weight-space|Weight Space]] decomposition. Each weight $w = \lambda - \delta$ (where $\delta \in Q_+$ is the weight offset from the highest weight) gives a block:

$$\rho_\lambda = \sum_{\delta \in Q_+} \frac{x^{\lambda - \delta}}{s_\lambda(x)} \cdot \Pi_{\lambda - \delta}$$

where $\Pi_{\lambda-\delta}$ is the projector onto the weight-$(\lambda - \delta)$ subspace, which has dimension $K_{\lambda, \lambda - \delta}$ (the [[definitions/kostka-number|Kostka Number]]).

The eigenvalue of $\rho_\lambda$ on the weight-$(\lambda - \delta)$ block is $x^{\lambda - \delta}/s_\lambda(x)$, where $x^w = x_1^{w_1} \cdots x_d^{w_d}$ is the monomial. This is a **classical probability** on the weight spaces, determined entirely by the spectrum $x$ of $\rho$.

**Key point:** $\rho_\lambda$ is diagonal in the weight basis but generally *not* in the [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin Basis]] within each weight space (though for 1-dimensional weight spaces, these coincide). The block structure means we can analyze the fidelity weight-by-weight in the [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] proof.

## Qubit Example ($d = 2$)

For a qubit ($d = 2$) with eigenvalues $x_1 = p$, $x_2 = 1-p$, the irrep $\lambda = (n/2 + J, n/2 - J)$ has dimension $2J + 1$. The weights are $w_k = (n/2 + J - k,\, n/2 - J + k)$ for $k = 0, 1, \ldots, 2J$.

Each weight space is **1-dimensional** (all Kostka numbers are 1 for $d = 2$), so $\rho_\lambda$ is fully diagonal:

$$\rho_\lambda = \sum_{k=0}^{2J} \frac{p^{n/2+J-k}(1-p)^{n/2-J+k}}{s_\lambda(p, 1-p)} |k\rangle\langle k|$$

The Schur polynomial is $s_\lambda(p, 1-p) = \sum_{k=0}^{2J} p^{n/2+J-k}(1-p)^{n/2-J+k}$, which is a truncated binomial sum. The eigenvalues decay geometrically from the highest weight ($k = 0$, eigenvalue $\propto p^{n/2+J}(1-p)^{n/2-J}$) to the lowest weight ($k = 2J$, eigenvalue $\propto p^{n/2-J}(1-p)^{n/2+J}$). For $p > 1/2$, most of the spectral mass concentrates near $k = 0$ (the highest weight).

## Connection to Proof Architecture

The normalized irrep state $\rho_\lambda$ is the object that the compression scheme must faithfully store and recover. The [[results/achievability|Achievability (State Compression)]] encodes $\rho_\lambda$ by applying the [[definitions/generalized-cloning-map-def|Generalized Cloning Map]] $\mathcal{C}_{\lambda \to \Lambda^*}(\rho_\lambda)$. The block-diagonal structure enables the weight-by-weight analysis in the [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] proof: the "classical part" of the fidelity depends on the eigenvalue ratios $x^{\mu-\delta}/x^{\nu-\delta}$ between corresponding weight blocks, while the "quantum part" depends on the alignment of weight subspaces.

## Used By

- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]]
- [[results/achievability|Achievability (State Compression)]]

## External References

- [Goodman and Wallach, *Symmetry, Representations, and Invariants* (Springer, 2009)](https://doi.org/10.1007/978-0-387-79852-3)
- [Irreducible representation (Wikipedia)](https://en.wikipedia.org/wiki/Irreducible_representation)
