# Semicircular Elements and Free Independence

**Context:** background for [[concepts/free-probability-theory|free probability]]. The current [[Letter|Letter]] discusses freeness, but its physical-entropy derivation does not use semicircular perturbations.

## Intuition

A semicircular element is a self-adjoint noncommutative random variable with the semicircle distribution. It plays the Gaussian's role in the free central limit theorem. This is background for the meaning of “free”; it is not the mechanism that produces the Letter's unitary-orbit volume formula.

## Formal Description

A standard centered, variance-one semicircular element $s$ in a tracial von Neumann algebra $(\mathcal A,\tau)$ has spectral measure

$$
d\mu_s(t)=\frac1{2\pi}\sqrt{4-t^2}\,\mathbf 1_{[-2,2]}(t)\,dt.
$$

Its moments satisfy

$$
\tau(s^{2k})=\frac1{k+1}\binom{2k}{k},
\qquad
\tau(s^{2k+1})=0.
$$

In particular, $\tau(s)=0$, $\tau(s^2)=1$, and $\tau(s^4)=2$. These are the Catalan even moments; see [Speicher's random-matrix course, Exercise 3](https://www.math.uni-sb.de/ag/speicher/lehre/ZMwise1920/ZMBlatt01.pdf).

The density is proportional to a semicircle and has compact support. The normalization here matters: rescaling $s$ changes its variance and support.

## Free Independence

Unital subalgebras $\mathcal A_i\subseteq\mathcal A$ are free if

$$
\tau(a_1\cdots a_m)=0
$$

whenever $a_j\in\mathcal A_{i_j}$, $\tau(a_j)=0$, and $i_j\ne i_{j+1}$ for every adjacent pair. The indices need not all be different.

The [Letter's discussion](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L260) uses this definition to distinguish free independence from tensor-product independence. It mentions temporal asymptotic freeness only in suitable large-system or large-$N$ chaotic limits.

A Haar rotation of a finite matrix does not by itself establish freeness of its “eigenvalues and eigenvectors.” Freeness concerns joint moments of specified algebras or operator families. A single unitary conjugation preserves the matrix's spectral distribution.

## Role in the Current Letter

The Letter's physical free entropy is an ambient Hilbert–Schmidt tube-volume ratio. Its End Matter evaluates this ratio using the [[concepts/vandermonde-determinant|Vandermonde Jacobian]], integration over eigenvalue blocks, Gaussian integrals, and radial integration. It does **not** obtain that formula by replacing $\rho$ with $\rho+\varepsilon s$.

Semicircular perturbations belong to the broader study of [[concepts/free-entropy-dimension|free entropy dimension]]. For the atomic spectrum, the Letter cites the dimension value

$$
\delta(\rho)=1-\frac1{d^2}\sum_a g_a^2
$$

and relates it to the orbit dimension. This connection should be distinguished from a claim that the Letter proves a semicircular-smearing expansion.

Likewise, the QMDL relation is established by combining the Article's representation-dimension result with the Letter's geometric calculation. The broader [[open-questions/free-entropy-conjecture|operator-programming conjecture]] is not a consequence of freeness alone.

The semicircular background and the Letter's volume calculation are outside the Article Theorems 1 and 2 Lean endpoints.

## Related

- [[concepts/free-probability-and-entropy|The entropy constructions]]
- [[concepts/free-entropy|Microstate free entropy]]
- [[concepts/free-entropy-dimension|Free entropy dimension]]
- [[concepts/physical-free-entropy|Physical free entropy]]
- [Speicher, Lecture Notes on Free Probability Theory](https://arxiv.org/abs/1908.08125)
