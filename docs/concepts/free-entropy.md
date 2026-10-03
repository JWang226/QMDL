# Free Entropy

**Appears in:** the current [[Letter|Letter]], with the compression result supplied by the [[Article|Article]].
**Source labels:** [eq:free_ent](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L106), [eq:free_ent_formula](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L125).

## Intuition

Voiculescu's microstate free entropy counts matrices whose moments approximate a tracial noncommutative distribution. Since the count uses continuous volume, it is closer to Shannon's **differential** entropy than to a discrete entropy.

It is distinct from von Neumann entropy. The latter is an entropy of a state; free entropy takes the moments of one or more operators in a tracial algebra as input. The Letter's operational statement uses a separate finite-dimensional quantity, [[concepts/physical-free-entropy|physical free entropy]], rather than substituting a density matrix directly into the large-matrix definition.

## Formal Description

Let $a$ be a bounded self-adjoint operator in a tracial von Neumann algebra $(\mathcal A,\tau)$. Fix $R>\|a\|$. Define

$$
\Gamma_R(a;m,\varepsilon,N)=
\left\{X\in M_N^{\mathrm{s.a.}}:
\|X\|\le R,\quad
\left|N^{-1}\operatorname{Tr}X^k-\tau(a^k)\right|\le\varepsilon
\text{ for every }1\le k\le m\right\}.
$$

With Hilbert–Schmidt Lebesgue volume and base-two logarithms,

$$
\chi(a)=\inf_m\inf_{\varepsilon>0}
\limsup_{N\to\infty}
\left[\frac12\log_2 N+
\frac1{N^2}\log_2\operatorname{Vol}\Gamma_R(a;m,\varepsilon,N)\right].
$$

The result is independent of the chosen cutoff $R>\|a\|$. The factor $N^{-2}$ reflects the $N^2$ real matrix coordinates; the additive $\frac12\log_2N$ removes a universal volume divergence. Moment matching is essential: an atomic empirical spectral measure does not approach a continuous measure in total variation, though it can approach it in moments or a weak metric.

For a single self-adjoint variable with spectral measure $\mu_a$, the Letter uses

$$
\chi(a)=
\iint_{\mathbb R^2}\log_2|s-t|\,d\mu_a(s)\,d\mu_a(t)
+\frac34\log_2e+\frac12\log_2(2\pi).
$$

The factor $\log_2e$ is required by the binary-log convention. The additive constant also depends on the stated volume normalization.

## Why the Logarithmic Energy Appears

In eigenvalue and eigenvector coordinates, Hermitian matrix volume has a squared [[concepts/vandermonde-determinant|Vandermonde factor]]:

$$
dX\ \propto\ \prod_{i<j}(\lambda_i-\lambda_j)^2\,d\lambda\,dU.
$$

Its normalized logarithm is

$$
\frac1{N^2}\log_2\Delta(\lambda)^2
=\frac1{N^2}\sum_{i\ne j}\log_2|\lambda_i-\lambda_j|,
$$

a discrete logarithmic energy. This geometric Jacobian, not an assertion that eigenvalues and eigenvectors are free random variables, explains the spectral-gap terms.

The Letter keeps the Lebesgue convention. Using a Gaussian reference measure instead introduces an additional quadratic-moment term, so the two functionals should not be identified without that correction.

## Finite-Dimensional Operators

For $\rho\in(M_d(\mathbb C),d^{-1}\operatorname{Tr})$,

$$
\mu_\rho=\frac1d\sum_{i=1}^d\delta_{p_i}.
$$

Every atom contributes a divergent self-interaction, hence $\chi(\rho)=-\infty$, even if all eigenvalues are distinct. Omitting coincident-eigenvalue terms defines the finite spectral expression

$$
\chi_{\mathrm{reg}}(\rho)
=2\sum_{\substack{i<j\\p_i\ne p_j}}\log_2|p_i-p_j|.
$$

Then $d^{-2}\chi_{\mathrm{reg}}$ is the logarithmic energy with those terms omitted. This convention is not an equality between the ordinary $\chi(\rho)$ and a finite entropy. The Letter instead defines a nonnegative finite-resolution tube-volume ratio.

## Role in the Project

For fixed dimension and distinct positive eigenvalues, the attaining known-spectrum compression sequence satisfies

$$
\log_2\dim M_n
=\frac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1).
$$

The exact offset is given on the [[concepts/physical-free-entropy|physical free entropy page]]. The resolution is $n^{-1}$ in this volume comparison; the local statistical distinguishability scale is $n^{-1/2}$. These scales have different roles.

The [[Article|Article]] and its Lean formalization prove the memory formula and optimality. They do not formalize the Letter's ambient-volume calculation or its bridge back to $\chi$.

## Why “Free”?

“Free” refers to free independence of subalgebras: alternating products of centered elements have zero trace. Free entropy is additive for freely independent families, subject to the relevant entropy hypotheses, as ordinary entropies are additive for independent tensor factors.

Conjugating a single matrix by a unitary preserves its spectral measure; it does not create a free convolution of its eigenvalues and eigenvectors. The Letter mentions asymptotic freeness of observables in suitable chaotic large-system limits as motivation for future dynamical applications. That is separate from the fixed-$d$, $n\to\infty$ compression proof.

## Related

- [[concepts/free-probability-and-entropy|Introduction to free probability and entropy]]
- [[definitions/free-entropy-voiculescu|Microstate definition]]
- [[concepts/physical-free-entropy|Finite-resolution physical free entropy]]
- [[definitions/regularized-free-entropy|Regularized spectral term]]
- [[concepts/free-entropy-dimension|Free entropy dimension]]
- [[concepts/quantum-minimum-description-length|The operational compression task]]
