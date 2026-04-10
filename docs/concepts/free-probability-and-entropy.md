# Introduction to Free Probability, Free Entropy, and Free Entropy Dimension

This page provides a self-contained introduction to the mathematical background from free probability theory used in this project.

---

## Part I: Free Probability

### Motivation

Free probability theory, developed by Dan Voiculescu beginning in the 1980s, is a noncommutative analogue of classical probability. Its original motivation was the **free group factors problem**: are the type $\mathrm{II}_1$ factors $L(\mathbb{F}_n)$ and $L(\mathbb{F}_m)$ isomorphic for $n \neq m$? (This remains open.) The theory gained broader significance when Voiculescu discovered (1991) that independent random matrices become **freely independent** in the large-$N$ limit.

### Noncommutative Probability Spaces

A **noncommutative probability space** is a pair $(\mathcal{A}, \varphi)$ where $\mathcal{A}$ is a unital algebra over $\mathbb{C}$ and $\varphi: \mathcal{A} \to \mathbb{C}$ is a linear functional with $\varphi(1) = 1$.

The most important setting is the **tracial $W^*$-probability space** $(M, \tau)$, where $M$ is a von Neumann algebra and $\tau$ is a faithful normal tracial state.

**Canonical example:** $(M_N(\mathbb{C}),\, \mathrm{tr}_N)$ where $\mathrm{tr}_N = \frac{1}{N}\mathrm{Tr}$ -- the space of random matrices.

### Free Independence

Unital subalgebras $\mathcal{A}_1, \ldots, \mathcal{A}_m \subseteq \mathcal{A}$ are **freely independent** if

$$\varphi(a_1 a_2 \cdots a_n) = 0$$

whenever each $a_j \in \mathcal{A}_{i(j)}$ with alternating indices $i(1) \neq i(2) \neq \cdots \neq i(n)$ and each $a_j$ is centered: $\varphi(a_j) = 0$.

**Key model:** If $A$ is a subalgebra and $U$ is a Haar-random unitary, then $A$ and $UAU^*$ are asymptotically free. This is why freeness governs the eigenbasis structure of random matrices.

### Free Cumulants and Noncrossing Partitions

Roland Speicher reformulated free probability using **free cumulants** and **noncrossing partitions** $\mathrm{NC}(n)$ (partitions with no crossing blocks, counted by Catalan numbers $C_n$). The moment-cumulant formula:

$$\varphi(a^n) = \sum_{\pi \in \mathrm{NC}(n)} \prod_{V \in \pi} \kappa_{|V|}(a, \ldots, a)$$

**Freeness criterion:** $X_1, \ldots, X_m$ are free iff all mixed free cumulants vanish.

### Key Distributions

**Semicircular (Wigner):** density $f(x) = \frac{1}{2\pi}\sqrt{4 - x^2}$ on $[-2, 2]$. Moments are Catalan numbers. Only $\kappa_2 \neq 0$. This is the **free Gaussian** -- the limit of sums of freely independent variables (free CLT). See [[concepts/semicircular-element|Semicircular Element and Free Independence]].

**Marchenko-Pastur (Free Poisson):** all free cumulants equal $\lambda$. Arises from Wishart matrices $\frac{1}{N}X^*X$.

### R-Transform and Free Convolution

The **R-transform** $R_\mu(z) = \sum_{n=1}^\infty \kappa_n z^{n-1}$ linearizes additive free convolution:

$$R_{\mu \boxplus \nu}(z) = R_\mu(z) + R_\nu(z)$$

This is the free analogue of the additivity of classical cumulant generating functions.

### The Random Matrix Connection

**Wigner's Semicircle Law:** Eigenvalues of $N \times N$ Wigner matrices converge to the semicircular distribution.

**Asymptotic Freeness (Voiculescu, 1991):** Independent GUE matrices are asymptotically free as $N \to \infty$.

**Significance for this project:** When $\rho^{\otimes n}$ is decomposed via the [[concepts/schur-weyl-duality|Schur-Weyl Duality]], eigenvalues and eigenvectors become freely independent in the large-$n$ limit. This is why [[concepts/free-entropy|Free Entropy]] -- not von Neumann entropy -- governs the [[concepts/quantum-minimum-description-length|QMDL]].

### Classical vs. Free

| Classical | Free |
|---|---|
| Independence: moments factorize | Freeness: alternating centered moments vanish |
| Gaussian | Semicircular |
| Shannon entropy | Free entropy |
| Fourier/MGF | R-transform |
| All partitions | Noncrossing partitions |
| Tensor products | Free products |

---

## Part II: Free Entropy

### Microstate Definition

For self-adjoint $X_1, \ldots, X_n$ in a tracial $W^*$-probability space $(M, \tau)$, the **microstate space** is:

$$\Gamma_R(X_1, \ldots, X_n;\, m, k, \varepsilon) = \left\{ (A_1, \ldots, A_n) \in (M_k^{sa})^n : \begin{array}{l} \|A_j\| < R, \\ \left|\tau(X_{i_1} \cdots X_{i_p}) - k^{-1}\mathrm{Tr}(A_{i_1} \cdots A_{i_p})\right| < \varepsilon \end{array} \right\}$$

for all $1 \le p \le m$ and all index tuples. The **free entropy** is:

$$\chi(X_1, \ldots, X_n) = \sup_R\, \inf_m\, \inf_\varepsilon\, \limsup_{k \to \infty}\left(k^{-2}\log\mathrm{vol}\,\Gamma_R + \frac{n}{2}\log k\right)$$

**Analogy:** Shannon entropy counts typical *sequences*; free entropy counts typical *matrices*.

### Closed-Form Formula

For a single self-adjoint $X$ with spectral measure $\mu$:

$$\chi(X) = \iint \log|s - t|\, d\mu(s)\, d\mu(t) + \frac{3}{4} + \frac{1}{2}\log 2\pi$$

The double integral $\Sigma(\mu) = \iint \log|s-t|\, d\mu(s)\, d\mu(t)$ is the **logarithmic energy**, arising from the [[concepts/vandermonde-determinant|Vandermonde determinant]] in random matrix eigenvalue densities.

For a $d$-dimensional density matrix $\rho$ with eigenvalues $p_1, \ldots, p_d$:

$$\chi(\rho) = \frac{2}{d^2}\sum_{i < j}\log|p_i - p_j| + \text{(divergent)}$$

The divergence motivates the [[concepts/physical-free-entropy|Physical Free Entropy]].

### Key Properties

| Property | Statement |
|----------|-----------|
| **Subadditivity** | $\chi(X_1, \ldots, X_{m+n}) \le \chi(X_1, \ldots, X_m) + \chi(X_{m+1}, \ldots, X_{m+n})$ |
| **Additivity under freeness** | If freely independent with finite $\chi$, then $\chi(X_1, \ldots, X_n) = \sum_j \chi(X_j)$ |
| **Maximum entropy** | Freely independent semicircular variables maximize $\chi$ among all with given second moments |

### Non-Microstate Free Entropy $\chi^*$

Voiculescu also defined $\chi^*$ using **free Fisher information** $\Phi^*$:

$$\chi^*(X_1, \ldots, X_n) = \frac{1}{2}\int_0^\infty \left(\frac{n}{1+t} - \Phi^*(X_1 + \sqrt{t}\,S_1, \ldots)\right)dt + \frac{n}{2}\log 2\pi e$$

The fundamental inequality $\chi \le \chi^*$ holds; equality for $n = 1$ is known; the general case is open.

### The Coulomb Gas Picture

The GUE joint eigenvalue density is $p(\lambda_1, \ldots, \lambda_N) \propto e^{-\frac{N}{2}\sum \lambda_i^2} \prod_{j<k}|\lambda_j - \lambda_k|^2$ -- a 2D Coulomb gas with logarithmic repulsion. By Ben Arous-Guionnet large deviations, free entropy is the rate function for random matrix ensembles at speed $N^2$.

### Applications in Operator Algebras

- **Primeness of free group factors (Ge, 1997):** $L(\mathbb{F}_n)$ cannot decompose as a tensor product.
- **Absence of Cartan subalgebras (Voiculescu, 1996):** $L(\mathbb{F}_n)$ has no Cartan subalgebra.

---

## Part III: Free Entropy Dimension

### Definition

$$\delta(a) = 1 + \limsup_{\varepsilon \to 0} \frac{\chi(a + \varepsilon s)}{-\log \varepsilon}$$

where $s$ is a freely independent semicircular element. The perturbation regularizes $\chi$, and the rate of divergence encodes a dimension. Always $0 \leq \delta(a) \leq 1$.

### Explicit Formula

For a $d$-dimensional operator with spectral multiplicities $g_1, \ldots, g_m$ (where $\sum g_i = d$):

$$\delta(\rho) = 1 - \frac{\sum_i g_i^2}{d^2}$$

The unnormalized version $d^2 \cdot \delta(\rho) = d^2 - \sum_i g_i^2$ counts real degrees of freedom: a $d \times d$ Hermitian matrix has $d^2$ parameters, and the stabilizer $\prod_i \mathrm{U}(g_i)$ has dimension $\sum_i g_i^2$.

### Derivation (Letter, Appendix A)

Adding $\varepsilon s$ smooths the point-mass spectrum via free additive convolution:

$$\chi(\rho + \varepsilon s) = \frac{\sum_i g_i^2}{d^2}\log \varepsilon + \chi_{\mathrm{reg}}(\rho) + \mathrm{const} + O(\varepsilon)$$

Substituting: $\delta(\rho) = 1 - \sum_i g_i^2/d^2$. The $\chi_{\mathrm{reg}}$ and constant vanish in the limit.

This connects to [[concepts/physical-free-entropy|Physical Free Entropy]]: $\chi_{\mathrm{phy}}(\rho;\varepsilon) = d^2\delta(\rho)\log(1/\varepsilon) + \chi_{\mathrm{reg}}(\rho) + \mathrm{const}$.

### Examples

| State | $\delta(\rho)$ | $d^2\delta$ | Geometric interpretation |
|-------|----------------|-------------|--------------------------|
| Non-degenerate ($g_i = 1$) | $(d-1)/d$ | $d(d-1)$ | Flag manifold $\mathrm{U}(d)/\mathrm{U}(1)^d$ |
| Maximally mixed ($g_1 = d$) | $0$ | $0$ | Invariant under all unitaries |
| Pure state ($g = 1, d-1$) | $2(d-1)/d^2$ | $2(d-1)$ | $\mathbb{CP}^{d-1}$ |
| Rank-$k$ projector ($g = k, d-k$) | $2k(d-k)/d^2$ | $2k(d-k)$ | Grassmannian $\mathrm{Gr}(k,d)$ |

### Role in QMDL

$$\log|M_n| = \frac{d^2 \cdot \delta(\rho)}{2} \log n + O(1)$$

The division by 2 is the geometric quantization factor from the [[concepts/kks-theorem|KKS Theorem]].

---

## References

**Free probability:**
- voiculescu1993analogues through voiculescu2002free: Voiculescu's foundational series
- speicher1996universal: Speicher on universal products
- hiai2000semicircle: Hiai-Petz textbook

**Free entropy:**
- ge1997applications, ge1998applications: Ge's applications
- arous1997large: Ben Arous-Guionnet large deviations
- Jung_2003, Jung_2006: Free entropy dimension

**Textbooks:**
- A. Nica and R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge (2006)
- J. Mingo and R. Speicher, *Free Probability and Random Matrices*, Springer (2017)
- D. Voiculescu, K. Dykema, and A. Nica, *Free Random Variables*, AMS (1992)

## Related

- [[concepts/free-probability-theory|Free Probability Theory]] -- role in this project
- [[concepts/free-entropy|Free Entropy]] -- central object of the project
- [[concepts/physical-free-entropy|Physical Free Entropy]] -- finite-dimensional regularized version
- [[definitions/regularized-free-entropy|Regularized Free Entropy]] -- the $O(1)$ correction
- [[concepts/semicircular-element|Semicircular Element and Free Independence]]
- [[concepts/vandermonde-determinant|Vandermonde Determinant]]

## External References

- [Free probability (Wikipedia)](https://en.wikipedia.org/wiki/Free_probability)
- [Free entropy (Wikipedia)](https://en.wikipedia.org/wiki/Free_entropy)
- [Voiculescu, "Free entropy" (survey, 2002)](https://doi.org/10.1112/S0024609301008992)
- [F. Hiai and D. Petz, *The Semicircle Law, Free Random Variables and Entropy*, AMS (2000)](https://bookstore.ams.org/view?ProductCode=SURV/77)
