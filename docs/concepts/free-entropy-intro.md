# Introduction to Free Entropy

This page provides a self-contained introduction to Voiculescu's free entropy for readers of this wiki. For its specific role in the project, see [[concepts/free-entropy|Free Entropy]].

---

## Motivation

Voiculescu introduced free entropy in the 1990s as part of his program to solve the **free group factors problem**: are $L(\mathbb{F}_n) \cong L(\mathbb{F}_m)$ for $n \neq m$? The idea was to construct invariants of von Neumann algebras by counting "microstates" -- matrix approximations -- just as Boltzmann entropy counts microstates in statistical mechanics.

The strategy succeeded partially: free entropy proved that free group factors have **no Cartan subalgebras** (Voiculescu 1996) and are **prime** (Ge 1997), even though the isomorphism problem remains open.

---

## The Microstate Definition

### Setup

Let $(M, \tau)$ be a tracial $W^*$-probability space and $X_1, \ldots, X_n \in M$ self-adjoint. Denote by $M_k^{sa}$ the real vector space of $k \times k$ self-adjoint matrices, equipped with Lebesgue measure from the Hilbert-Schmidt inner product.

### Microstate Space

For $R > 0$, $m \in \mathbb{N}$, $k \in \mathbb{N}$, $\varepsilon > 0$:

$$\Gamma_R(X_1, \ldots, X_n;\, m, k, \varepsilon) = \left\{ (A_1, \ldots, A_n) \in (M_k^{sa})^n : \begin{array}{l} \|A_j\| < R, \\ \left|\tau(X_{i_1} \cdots X_{i_p}) - k^{-1}\mathrm{Tr}(A_{i_1} \cdots A_{i_p})\right| < \varepsilon \end{array} \right\}$$

for all $1 \le p \le m$ and all tuples $(i_1, \ldots, i_p) \in \{1, \ldots, n\}^p$.

In words: $\Gamma_R$ is the set of all $n$-tuples of $k \times k$ self-adjoint matrices whose mixed moments up to order $m$ approximate those of $X_1, \ldots, X_n$ within $\varepsilon$.

### Free Entropy

$$\chi(X_1, \ldots, X_n) = \sup_R\, \inf_m\, \inf_\varepsilon\, \limsup_{k \to \infty}\left(k^{-2}\log\mathrm{vol}\,\Gamma_R + \frac{n}{2}\log k\right)$$

The normalization $k^{-2}$ accounts for the $O(k^2)$ real degrees of freedom in a $k \times k$ Hermitian matrix. The additive $\frac{n}{2}\log k$ removes a universal divergence. The value $\chi \in [-\infty, +\infty)$.

**Analogy with Boltzmann entropy:** Shannon entropy counts typical *sequences*; free entropy counts typical *matrices*. Shannon entropy uses the counting measure on $\{1,\ldots,d\}^N$; free entropy uses Lebesgue measure on $(M_k^{sa})^n$.

---

## Closed-Form Formula (Single Variable)

For a single self-adjoint $X$ with spectral measure $\mu$:

$$\chi(X) = \iint \log|s - t|\, d\mu(s)\, d\mu(t) + \frac{3}{4} + \frac{1}{2}\log 2\pi$$

The double integral $\Sigma(\mu) = \iint \log|s-t|\, d\mu(s)\, d\mu(t)$ is the **logarithmic energy** of $\mu$. This quantity appears naturally in potential theory and random matrix theory: the Vandermonde determinant $\prod_{i<j}|\lambda_i - \lambda_j|^2$ in the eigenvalue density of GUE gives rise to exactly this logarithmic interaction.

**Maximum:** Among distributions with variance $\sigma^2$, $\chi$ is maximized by the [[concepts/semicircular-element|semicircular distribution]], giving $\chi(S) = \frac{1}{2}\log 2\pi e\sigma^2$. This parallels the Gaussian maximizing Shannon's differential entropy.

### Finite-Dimensional Density Matrix

For $\rho$ with eigenvalues $p_1, \ldots, p_d$, the spectral measure is $\mu_\rho = \frac{1}{d}\sum_i \delta(x - p_i)$, so:

$$\chi(\rho) = \frac{2}{d^2}\sum_{i < j}\log|p_i - p_j| + \text{(divergent constant)}$$

The divergence comes from point masses colliding in the double integral. This motivates the [[concepts/physical-free-entropy|Physical Free Entropy]], which introduces a resolution $\varepsilon$ to obtain a finite, operationally meaningful quantity.

---

## Key Properties

| Property | Statement |
|----------|-----------|
| **Subadditivity** | $\chi(X_1, \ldots, X_{m+n}) \le \chi(X_1, \ldots, X_m) + \chi(X_{m+1}, \ldots, X_{m+n})$ |
| **Additivity under freeness** | If $X_1, \ldots, X_n$ are freely independent with finite $\chi$, then $\chi(X_1, \ldots, X_n) = \sum_j \chi(X_j)$ |
| **Upper semicontinuity** | $\chi$ is upper semicontinuous in distribution |
| **Maximum entropy** | Freely independent semicircular variables maximize $\chi$ among all with given second moments |
| **No atoms** | If $\chi(X_1, \ldots, X_n) > -\infty$, then $W^*(X_1, \ldots, X_n)$ is diffuse (no atoms) |

The additivity under freeness parallels Shannon entropy being additive under independence, and is the deepest reason why free entropy governs the compression of density matrices in this project.

---

## Free Entropy Dimension

**Definition.** Let $S_1, \ldots, S_n$ be standard semicircular elements, freely independent from $\{X_1, \ldots, X_n\}$. The **free entropy dimension** is:

$$\delta(X_1, \ldots, X_n) = n + \limsup_{\varepsilon \downarrow 0}\frac{\chi(X_1 + \varepsilon S_1, \ldots, X_n + \varepsilon S_n)}{|\log\varepsilon|}$$

The semicircular perturbation regularizes $\chi$ (which may be $-\infty$), and the rate of divergence as $\varepsilon \to 0$ encodes a dimension.

**Basic property:** $\delta(X_1, \ldots, X_n) \le n$, with equality for freely independent semicircular elements.

See [[concepts/free-entropy-dimension|Free Entropy Dimension]] for its role in this project.

---

## Non-Microstate Free Entropy $\chi^*$

Voiculescu also defined a **non-microstate** version $\chi^*$ using **free Fisher information** $\Phi^*$, the free analogue of Fisher information. The conjugate variable $\mathcal{J}(X : B)$ plays the role of the classical score function $(\log p)'$.

$$\chi^*(X_1, \ldots, X_n) = \frac{1}{2}\int_0^\infty \left(\frac{n}{1+t} - \Phi^*(X_1 + \sqrt{t}\,S_1, \ldots, X_n + \sqrt{t}\,S_n)\right)dt + \frac{n}{2}\log 2\pi e$$

The fundamental inequality $\chi \le \chi^*$ was proved by Biane, Capitaine, and Guionnet. Whether $\chi = \chi^*$ always holds is a major open problem; equality is known for a single variable ($n = 1$).

---

## Connection to Random Matrix Theory

### The Coulomb Gas Picture

For the GUE, the joint eigenvalue density is:

$$p(\lambda_1, \ldots, \lambda_N) \propto \exp\!\left(-\frac{N}{2}\sum_i \lambda_i^2\right) \prod_{j < k}|\lambda_j - \lambda_k|^2$$

In logarithm: a quadratic confining potential plus logarithmic repulsion -- a **2D Coulomb gas** on the real line. The $\prod|\lambda_j - \lambda_k|^2$ is the squared [[concepts/vandermonde-determinant|Vandermonde determinant]].

### Large Deviations (Ben Arous--Guionnet)

The empirical spectral measure $L_N = N^{-1}\sum_i \delta_{\lambda_i}$ satisfies a large deviation principle at speed $N^2$ with rate function:

$$\Phi(\mu) = \int V\, d\mu - \iint \log|s-t|\, d\mu(s)\, d\mu(t)$$

The second term is precisely the logarithmic energy appearing in $\chi$. The minimizer for $V(x) = x^2/2$ is the semicircle law.

**The bridge:** Free entropy is the large-deviations rate function for random matrix ensembles. The normalization $k^{-2}\log\mathrm{vol}$ in the definition of $\chi$ matches the speed $N^2$ in the LDP.

---

## Applications in Operator Algebras

**Primeness of free group factors (Ge, 1997).** $L(\mathbb{F}_n)$ cannot be decomposed as a tensor product of two $\mathrm{II}_1$ factors for $n \geq 2$. Proof: tensor decomposition forces $\chi = -\infty$ for generators, contradicting finiteness of $\chi$ (established via GUE microstates).

**Absence of Cartan subalgebras (Voiculescu, 1996).** $L(\mathbb{F}_n)$ has no Cartan subalgebra. The microstate volume is too constrained by approximate Cartan subalgebra conditions to be compatible with finite free entropy.

**Free entropy dimension and property $\Gamma$.** If $\delta_0(X_1, \ldots, X_n) > 1$ for generators of a $\mathrm{II}_1$ factor $M$, then $M$ does not have property $\Gamma$.

---

## References

**Foundational papers (in project bibliography):**
- voiculescu1993analogues: Free entropy I -- microstate definition
- voiculescu1994analogues: Free entropy II -- properties and applications
- voiculescu1996analogues: Free entropy III -- absence of Cartan subalgebras
- voiculescu1998analogues: Free entropy V -- noncommutative Hilbert transforms ($\chi^*$)
- voiculescu2002free: Survey on free entropy
- ge1997applications, ge1998applications: Ge's applications to von Neumann algebras
- arous1997large: Ben Arous-Guionnet large deviations
- hiai2000semicircle: Hiai-Petz textbook

**Additional references:**
- hiai1998maximizing: Maximizing free entropy
- Jung_2003, Jung_2003_lemma, Jung_2006: Free entropy dimension results

## Related

- [[concepts/free-entropy|Free Entropy]] -- role in this project
- [[concepts/physical-free-entropy|Physical Free Entropy]] -- the finite-dimensional, regularized version
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- leading-order scaling
- [[definitions/free-entropy-voiculescu|Free Entropy (Voiculescu, Formal Definition)]]
- [[definitions/regularized-free-entropy|Regularized Free Entropy]]
- [[concepts/free-probability-basics|Introduction to Free Probability]] -- companion page
- [[concepts/vandermonde-determinant|Vandermonde Determinant]] -- eigenvalue repulsion

## External References

- [Free entropy (Wikipedia)](https://en.wikipedia.org/wiki/Free_entropy)
- [Free probability (Wikipedia)](https://en.wikipedia.org/wiki/Free_probability)
- [Voiculescu, "Free entropy" (survey, 2002)](https://doi.org/10.1112/S0024609301008992)
- [F. Hiai and D. Petz, *The Semicircle Law, Free Random Variables and Entropy*, AMS (2000)](https://bookstore.ams.org/view?ProductCode=SURV/77)
