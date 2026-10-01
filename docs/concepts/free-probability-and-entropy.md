# Free Probability and the Entropy Constructions

**Appears in:** the current [[Letter|Letter]], introduction and discussion.
**Source:** [letter.tex](https://github.com/JWang226/QMDL/blob/main/letter.tex).

## Intuition

The Letter distinguishes two ways to pass from classical entropy to a noncommutative setting. One replaces a probability distribution by a density operator, leading to von Neumann entropy. The other replaces typical strings by matrix microstates, leading to Voiculescu's free entropy.

The project then introduces a third object: a finite-resolution volume count around a finite-dimensional unitary orbit. This **physical free entropy** is the one related to the memory needed to encode an unknown eigenbasis with known spectrum.

## 1. Tracial Probability and Freeness

A tracial noncommutative probability space provides an algebra of operators and a normalized trace $\tau$. For finite matrices the example used by the Letter is

$$
(M_d(\mathbb C),\tau),\qquad \tau(A)=d^{-1}\operatorname{Tr}A.
$$

The distribution of a self-adjoint operator $a$ is specified by its moments $\tau(a^k)$, equivalently by its spectral measure. For a density matrix this measure assigns weight $1/d$ to each eigenvalue, counting multiplicity. It is different from the probability vector of eigenvalues used in $S(\rho)=-\operatorname{Tr}\rho\log_2\rho$.

Subalgebras $\mathcal A_i$ are freely independent when

$$
\tau(a_1\cdots a_m)=0
$$

whenever $a_j\in\mathcal A_{i_j}$, $\tau(a_j)=0$, and **adjacent** indices differ: $i_j\ne i_{j+1}$. All the indices need not be pairwise distinct.

This notion governs mixed moments and differs from tensor-product independence. Appropriate large-matrix models can converge to free families. The current Letter does not assume that the eigenvalues and eigenvectors of $\rho^{\otimes n}$ become freely independent, and the compression proof does not require such a limit.

## 2. Three Counting Constructions

| Quantity | Microstates or approximants | What the logarithm measures |
| --- | --- | --- |
| Shannon entropy | Strings whose empirical frequencies approach $p$ | Typical-string count per symbol |
| Von Neumann entropy | Subspaces capturing almost all mass of $\rho^{\otimes N}$ | Typical-subspace dimension per copy |
| Microstate free entropy | Hermitian matrices matching all moments through order $m$ | Renormalized large-matrix Lebesgue volume |

In [eq:shannon](https://github.com/JWang226/QMDL/blob/main/letter.tex#L86), the Letter writes

$$
H(p)=\inf_{\varepsilon>0}\lim_{N\to\infty}\frac1N
\log_2\#\{x^N:\|p_{x^N}-p\|_1\le\varepsilon\}.
$$

The [von Neumann counterpart](https://github.com/JWang226/QMDL/blob/main/letter.tex#L94) minimizes $\log_2\dim V$ over subspaces whose projector captures at least $1-\varepsilon$ of the source. At finite $N$, the smallest such subspace need not equal a frequency-window typical subspace, although their asymptotic rates agree.

For one bounded self-adjoint $a$, fix an operator-norm cutoff $R>\|a\|$. The [matrix microstate definition](https://github.com/JWang226/QMDL/blob/main/letter.tex#L106) is

$$
\chi(a)=\inf_m\inf_{\varepsilon>0}\limsup_{N\to\infty}
\left[\frac12\log_2N+\frac1{N^2}\log_2\operatorname{Vol}\Gamma_R(a;m,\varepsilon,N)\right],
$$

where every moment through order $m$ must match within tolerance. Volume makes this analogous to **differential** entropy. The [[concepts/free-entropy|free entropy page]] specifies $\Gamma_R$ and explains the normalization.

For several operators, moment constraints must also specify mixed noncommutative words. The Letter discusses this richer theory as a direction for general operator programming, not as an established multivariable QMDL theorem.

## 3. Spectral Energy and Finite Resolution

For a single variable,

$$
\chi(a)=\iint\log_2|s-t|\,d\mu_a(s)\,d\mu_a(t)
+\frac34\log_2e+\frac12\log_2(2\pi).
$$

The logarithmic energy comes from the squared Vandermonde Jacobian in matrix volume. A finite-dimensional spectral measure is atomic, making this ordinary free entropy $-\infty$.

The Letter holds the matrix dimension fixed and defines instead

$$
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=\log_2\frac{\operatorname{Vol}(\Omega_\varepsilon)}
{\operatorname{Vol}(B_\varepsilon^{d^2})},
\qquad
\Omega_\varepsilon=
\{X\in M_d^{\mathrm{s.a.}}:\|\lambda(X)-p\|_2\le\varepsilon\}.
$$

This is the exact volume ratio, not the exact logarithm of a covering number. Its ambient tube includes non-density matrices. The choice fixes the order-one normalization needed for the memory comparison.

If the distinct spectral levels have multiplicities $g_a$, put

$$
N_\rho=d^2-\sum_a g_a^2.
$$

For resolution smaller than half the smallest distinct spectral gap,

$$
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=N_\rho\log_2\varepsilon^{-1}
+\chi_{\mathrm{reg}}(\rho)
+C_{d,(g_a)}
+O_d(\varepsilon^2/g^2).
$$

The [[concepts/physical-free-entropy|physical free entropy page]] gives the complete constant and derivation. The normalized orbit dimension $N_\rho/d^2$ equals the single-variable free entropy dimension of the atomic spectral measure.

| Spectrum | Real orbit dimension $N_\rho$ |
| --- | --- |
| All eigenvalues distinct | $d^2-d$ |
| Scalar operator | $0$ |
| Pure state, $d\ge2$ | $2(d-1)$ |
| Two spectral levels with multiplicities $k,d-k$ | $2k(d-k)$ |

The geometry formula covers arbitrary multiplicities. It should not be read as a proved optimal-memory formula for every such spectrum.

## 4. The Operational Connection

For the known-spectrum orbit family with distinct positive eigenvalues, the Letter combines the Article's optimal memory formula with its volume calculation:

$$
\log_2\dim M_n
=\frac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1)
$$

for an attaining sequence. Every reliable sequence obeys the matching lower bound through the additive constant. No purification must be preserved, and the whole $n$-copy trace error must vanish.

The factor $1/2$ is consistent with the squared spectral-gap product in Hilbert–Schmidt volume and the first-power gap product in the Weyl dimension formula. The comparison resolution $n^{-1}$ is distinct from the statistical angular scale $n^{-1/2}$.

The End Matter's [double-scaling remark](https://github.com/JWang226/QMDL/blob/main/letter.tex#L314) relates physical free entropy back to $\chi$ only under explicit regularity, discrete-energy convergence, and resolution assumptions. It is not an unrestricted interchange of large-dimension and small-resolution limits.

## Role in the Project

The [[Article|Article]] establishes compression and cloning; the [[Letter|Letter]] interprets the optimal memory geometrically. The checked Lean proof covers Article Theorems 1 and 2. It does not certify all the free-probability background, the Letter's tube-volume formulas, or its proposed general programming applications.

Free entropy's additivity for free families and its subadditivity motivate a possible description-length theory for several operators. The Letter treats this as a research direction. Its discussion of asymptotic temporal freeness also requires suitable large-system or large-$N$ chaotic limits.

## Related

- [[concepts/free-entropy|Microstate free entropy]]
- [[concepts/physical-free-entropy|Physical free entropy and its constants]]
- [[concepts/free-entropy-dimension|Free entropy dimension]]
- [[concepts/free-probability-theory|Free probability theory]]
- [[concepts/schumacher-compression|Schumacher compression]]
- [[concepts/quantum-minimum-description-length|Quantum minimum description length]]
- [[open-questions/free-entropy-conjecture|Broader programming conjecture]]
