# Vandermonde Determinant

**Appears in:** the current [[Letter|Letter]], main text and End Matter, and the [[Article|Article]].
**Source labels:** [eq:hs_volume_element](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L285), [eq:weyl_geometry](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L228).

## Definition and Sign Convention

Use the Letter's convention

$$
\Delta(x)=\prod_{1\le i<j\le d}(x_i-x_j).
$$

With descending powers in the rows,

$$
\Delta(x)=\det[x_j^{\,d-i}]_{i,j=1}^d.
$$

The matrix with ascending powers $1,x_j,\ldots,x_j^{d-1}$ instead has determinant $\prod_{i<j}(x_j-x_i)=(-1)^{\binom d2}\Delta(x)$. The sign disappears in $\Delta^2$, but matters when writing character ratios. For decreasing distinct eigenvalues, the Letter's $\Delta$ is positive.

## Hilbert–Schmidt Volume: Squared Gaps

Write a Hermitian matrix with distinct, decreasing eigenvalues as $X=U\operatorname{diag}(\lambda)U^\dagger$. With normalized invariant measure $d\nu(U)$ on $\mathrm U(d)/\mathrm U(1)^d$, the Letter's exact Jacobian is

$$
dX=\frac{(2\pi)^{d(d-1)/2}}{\prod_{k=1}^{d-1}k!}
\Delta(\lambda)^2\,d\lambda_1\cdots d\lambda_d\,d\nu(U).
$$

The factor is $(2\pi)^{d(d-1)/2}$, not $\pi^{d(d-1)/2}$, for the stated Hilbert–Schmidt metric. Each complex off-diagonal direction has two real coordinates; the eigenvalue gap scales both, yielding a squared factor.

This is a change-of-coordinates formula. It does not require an assertion that eigenvalues and eigenvectors are freely independent. For unitarily invariant ensembles with a density relative to this volume, the Jacobian gives the familiar squared-gap eigenvalue repulsion.

For a matrix with $N$ eigenvalues, its normalized logarithm,

$$
N^{-2}\log_2\Delta(\lambda)^2
=N^{-2}\sum_{i\ne j}\log_2|\lambda_i-\lambda_j|,
$$

is the discrete logarithmic energy appearing in [[concepts/free-entropy|microstate free entropy]]. A Gaussian reference density would additionally contribute a quadratic potential.

## Physical Free Entropy: an Exact Volume Ratio

The Letter defines

$$
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=\log_2\frac{\operatorname{Vol}(\Omega_\varepsilon)}
{\operatorname{Vol}(B_\varepsilon^{d^2})},
$$

where $\Omega_\varepsilon$ is the full Hermitian-space tube around the unitary orbit. This is an exact definition; covering-number logarithms agree only up to $O(1)$ at fixed dimension.

For distinct eigenvalues and $\varepsilon<g/2$, integration over the centered eigenvalue ball cancels the linear Taylor term. The result is

$$
\begin{aligned}
\chi_{\mathrm{phy}}(\rho;\varepsilon)
={}&(d^2-d)\log_2\varepsilon^{-1}
+\log_2\Delta(p)^2
-\sum_{k=1}^{d-1}\log_2(k!)\\
&+\log_2\frac{\Gamma(d^2/2+1)}{\Gamma(d/2+1)}
+\frac{d(d-1)}2\log_2 2
+O_d(\varepsilon^2/g^2).
\end{aligned}
$$

The $\pi$ powers cancel after division by the reference-ball volume; the power of $2$ remains. The [[concepts/physical-free-entropy|physical entropy page]] derives the full expression.

When spectral levels have multiplicities $g_a$, evaluating $\Delta(p)$ directly gives zero and is not the correct tube asymptotic. Split the nearby Vandermonde into inter-block and intra-block factors. The former give

$$
\prod_{a<b}(p_a-p_b)^{2g_ag_b},
$$

while the latter supply extra powers of $\varepsilon$. The orbit coefficient becomes $d^2-\sum_a g_a^2$, and the regularized spectral term omits coincident-eigenvalue pairs.

## Weyl Dimension: First-Power Shifted Gaps

For a dominant row $\lambda$, set $a_i=\lambda_i+d-i$ and $b_i=d-i$. The exact [[concepts/weyl-dimension-formula|Weyl dimension formula]] is

$$
\dim\mathcal H_\lambda
=\frac{\Delta(a)}{\Delta(b)}
=\prod_{i<j}\frac{\lambda_i-\lambda_j+j-i}{j-i},
\qquad
\Delta(b)=\prod_{k=1}^{d-1}k!.
$$

If $\Lambda_i/n\to p_i$ with distinct decreasing limits, then

$$
\dim\mathcal H_\Lambda
=[1+o(1)]\,
\frac{n^{d(d-1)/2}\Delta(p)}
{\prod_{k=1}^{d-1}k!}.
$$

The squared gap product in Hilbert–Schmidt volume and the first-power product in this dimension asymptotic explain the matching spectrum-dependent terms after taking half of the physical entropy. The Letter also describes how the KKS symplectic form pairs the two real tangent directions, giving one gap per pair.

This comparison is **not** a literal identity saying that symplectic volume or representation dimension is the square root of Hilbert–Schmidt volume. The volume forms have different normalization constants; Weyl dimensions have integer-weight shifts, and physical entropy also includes a tube radius and a reference-cell volume. The precise relation is

$$
\log_2\dim M_n
=\frac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1)
$$

for the attaining code and the spectra covered by the Letter.

## Schur Characters

For a dominant nonnegative integral row $\lambda$, with the same descending-power convention,

$$
s_\lambda(x)=\frac{\det[x_j^{\,\lambda_i+d-i}]_{i,j=1}^d}{\Delta(x)}.
$$

For distinct $x_i$ this is a quotient of alternants. When two variables coincide, two **columns** of the numerator coincide; algebraically the Vandermonde divides the alternating numerator, yielding a polynomial that extends to all $x$. Its value at $(1,\ldots,1)$ is the representation dimension. See [[concepts/schur-polynomials|Schur polynomials]].

## Formalization Scope

The Article's Lean development proves the actual character and dimension identities and the memory asymptotic; see [[results/lemmas/weyl-dimension-asymptotic|the checked dimension route]]. The Letter's Hilbert–Schmidt Jacobian, tube-volume constants, and geometric comparison are separate mathematical content, not additional certified conclusions of those Lean endpoints.

## Related

- [[concepts/free-entropy|Logarithmic energy]]
- [[concepts/physical-free-entropy|Tube volumes and exact constants]]
- [[definitions/regularized-free-entropy|Regularized spectral term]]
- [[concepts/schur-polynomials|Schur characters]]
- [[concepts/weyl-dimension-formula|Weyl dimension formula]]
- [[concepts/free-entropy-dimension|Multiplicity-dependent dimension]]
