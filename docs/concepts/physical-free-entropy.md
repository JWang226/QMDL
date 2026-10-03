# Physical Free Entropy

**Appears in:** the current [[Letter|Letter]], with the compression theorem supplied by the [[Article|Article]].
**Source labels:** [eq:free_phys_def](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L146), [eq:free_phys1_app](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L298), [eq:degenerate_free_ent](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L380).

## Intuition

Physical free entropy counts resolution cells around the unitary orbit of a fixed finite-dimensional self-adjoint operator. The Letter defines this effective count by an **exact volume ratio**, which fixes its additive constant. A covering-number logarithm has the same small-resolution growth up to $O(1)$ at fixed dimension, but is not the definition.

Unlike ordinary [[concepts/free-entropy|microstate free entropy]], this quantity is finite and nonnegative for finite-dimensional operators. For the spectra covered by the compression theorem, half of it at resolution $n^{-1}$ gives the optimal memory cost up to an explicit dimension-and-rank constant.

All logarithms below are base two.

## Formal Description

Order the eigenvalues of $\rho$ as $p_1\ge\cdots\ge p_d$, and order the eigenvalues $\lambda(X)$ of each Hermitian $X$ the same way. For every $\varepsilon>0$, set

$$
\Omega_\varepsilon=
\left\{X\in M_d^{\mathrm{s.a.}}:
\|\lambda(X)-p\|_2\le\varepsilon\right\},
\qquad
\chi_{\mathrm{phy}}(\rho;\varepsilon)=
\log_2\frac{\operatorname{Vol}(\Omega_\varepsilon)}
{\operatorname{Vol}(B_\varepsilon^{d^2})}.
$$

The volume is Lebesgue volume induced by the Hilbert–Schmidt inner product on the full real vector space of Hermitian matrices. Thus

$$
\operatorname{Vol}(B_\varepsilon^{d^2})
=\frac{\pi^{d^2/2}\varepsilon^{d^2}}{\Gamma(d^2/2+1)}.
$$

Hoffman–Wielandt and eigenbasis alignment give

$$
\min_{U\in\mathrm U(d)}\|X-U\rho U^\dagger\|_2
=\|\lambda(X)-p\|_2.
$$

Consequently $\Omega_\varepsilon$ is precisely the Hilbert–Schmidt tube around the orbit. It is not restricted to positive or trace-one matrices. It contains the radius-$\varepsilon$ ball centered at $\rho$, so $\chi_{\mathrm{phy}}\ge0$. For a scalar operator the orbit is a point and the ratio is exactly one, giving $\chi_{\mathrm{phy}}=0$; the Letter states that equality occurs only in this case.

The small-gap condition $\varepsilon<g/2$ is needed for the expansions below, **not** for the definition. Here $g$ is the smallest gap between distinct spectral levels, with $g=\infty$ for a scalar operator.

## Distinct Eigenvalues: the Full Constant

For $p_1>\cdots>p_d$, [eq:free_phys1_app](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L298) gives

$$
\begin{aligned}
\chi_{\mathrm{phy}}(\rho;\varepsilon)
={}&(d^2-d)\log_2\varepsilon^{-1}
+2\sum_{i<j}\log_2|p_i-p_j|\\
&-\sum_{k=1}^{d-1}\log_2(k!)
+\log_2\frac{\Gamma(d^2/2+1)}{\Gamma(d/2+1)}
+\frac{d(d-1)}2\log_2 2\\
&+O_d(\varepsilon^2/g^2).
\end{aligned}
$$

The factor $\log_2 2=1$ is retained to make the volume normalization visible.

### Derivation

With decreasingly ordered eigenvalues and normalized invariant measure on $\mathrm U(d)/\mathrm U(1)^d$, the exact [Hilbert–Schmidt volume element](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L285) is

$$
dX=\frac{(2\pi)^{d(d-1)/2}}{\prod_{k=1}^{d-1}k!}
\Delta(\lambda)^2\,d\lambda_1\cdots d\lambda_d\,d\nu(U).
$$

For $\varepsilon<g/2$, the eigenvalue ball remains in the ordered chamber. Taylor expansion of $\Delta(\lambda)^2$ around $p$ has no linear contribution after integration over the centered ball. Hence

$$
\operatorname{Vol}(\Omega_\varepsilon)=
\frac{(2\pi)^{d(d-1)/2}}{\prod_{k=1}^{d-1}k!}
\frac{\pi^{d/2}\varepsilon^d}{\Gamma(d/2+1)}
\Delta(p)^2\,[1+O_d(\varepsilon^2/g^2)].
$$

Divide by the ambient reference-ball volume and take logarithms. The powers of $\pi$ cancel, but the factor $2^{d(d-1)/2}$ remains. Omitting that factor would change the claimed order-one memory offset.

## General Spectral Multiplicities

Let the distinct levels be $p_1>\cdots>p_m$ with multiplicities $g_1,\ldots,g_m$. Write

$$
\kappa=\sum_{a=1}^m g_a^2,\qquad
N_\rho=d^2-\kappa.
$$

The End Matter proves

$$
\begin{aligned}
\chi_{\mathrm{phy}}(\rho;\varepsilon)
={}&N_\rho\log_2\varepsilon^{-1}
+2\sum_{a<b}g_ag_b\log_2|p_a-p_b|\\
&+\frac{N_\rho}{2}\log_2 2
+\log_2\frac{\Gamma(d^2/2+1)}{\Gamma(\kappa/2+1)}\\
&+\sum_a\sum_{k=1}^{g_a-1}\log_2(k!)
-\sum_{k=1}^{d-1}\log_2(k!)
+O_d(\varepsilon^2/g^2).
\end{aligned}
$$

The spectral term is

$$
\chi_{\mathrm{reg}}(\rho)
=2\sum_{\substack{i<j\\p_i\ne p_j}}\log_2|p_i-p_j|,
$$

where this last sum uses the full eigenvalue list with multiplicities. The real orbit dimension is $N_\rho$, and $N_\rho/d^2$ is the atomic single-variable [[concepts/free-entropy-dimension|free entropy dimension]].

In the derivation, intra-block Vandermonde factors and the eigenvalue measure together contribute $\varepsilon^\kappa$. Inter-block gaps give the displayed spectral product. A blockwise sign-reversal symmetry cancels the linear error term; Gaussian integration followed by radial integration evaluates the remaining constant. This is the Letter's tube-volume derivation, not a semicircular-noise regularization argument.

These are fixed-dimension, fixed-spectrum expansions. They are not uniform through eigenvalue collisions. One must use the appropriate multiplicity formula at a collision rather than substitute a zero gap into the distinct-eigenvalue expansion.

## QMDL and the Rank-Deficient Case

For rank $r$ with distinct positive eigenvalues and a zero block of multiplicity $d-r$,

$$
N_\rho=r(2d-r-1),\qquad \kappa=(d-r)^2+r,
$$

and

$$
\chi_{\mathrm{reg}}(\rho)
=2\sum_{i<j\le r}\log_2|p_i-p_j|
+2(d-r)\sum_{i=1}^r\log_2p_i.
$$

Combining the geometric expansion with the Article's optimal memory formula gives, for an attaining sequence,

$$
\log_2\dim M_n
=\frac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1),
$$

where

$$
C_{d,r}
=-\frac12\sum_{k=d-r}^{d-1}\log_2(k!)
-\frac{N_\rho}{4}\log_2 2
-\frac12\log_2\frac{\Gamma(d^2/2+1)}{\Gamma(\kappa/2+1)}.
$$

For a fixed qubit spectrum $(p,1-p)$, $p>1/2$,

$$
\frac12\chi_{\mathrm{phy}}(\rho;n^{-1})
=\log_2n+\log_2(2p-1)+1+O(n^{-2}),
$$

and $C_{2,2}=-1$. This recovers the optimal memory $\log_2n+\log_2(2p-1)+o(1)$.

For pure states, $N_\rho=2d-2$ and every nonzero spectral gap is one. The memory formula becomes

$$
\log_2\dim M_n
=(d-1)\log_2n-\log_2((d-1)!)+o(1),
$$

consistent with the symmetric-subspace dimension $\binom{n+d-1}{d-1}$.

The factor $1/2$ reflects the squared spectral-gap product in Hilbert–Schmidt volume and the first-power product in the Weyl dimension formula. The chosen volume resolution $n^{-1}$ is not an estimation precision for each eigenbasis parameter; the local statistical scale is $n^{-1/2}$.

## Relation to Voiculescu's Entropy

The Letter's [rem:bridge](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L314) considers self-adjoint matrices $X_d$ whose eigenvalues are quantiles of a compactly supported measure $\mu_x$ with finite logarithmic energy. It assumes nonzero quantile gaps, convergence of the discrete logarithmic energies, and

$$
\varepsilon_d\to0,\qquad
\varepsilon_d=o(g_d),\qquad
\log_2\varepsilon_d^{-1}=o(d).
$$

Under these conditions,

$$
\begin{aligned}
\chi(x)
={}&\lim_{d\to\infty}\left[
d^{-2}\chi_{\mathrm{phy}}(X_d;\varepsilon_d)
-\log_2\varepsilon_d^{-1}-\frac12\log_2d\right]\\
&+\frac12\log_2e+\frac12\log_2(2\pi).
\end{aligned}
$$

The factor $d^{-2}$ belongs to this large-dimension bridge; physical free entropy itself is unnormalized. The assumptions control both near-collisions and the logarithmic-energy limit. This is not an unconditional exchange of the dimension and resolution limits.

## Role in the Project and Formalization Scope

The Letter derives these geometric formulas, including arbitrary spectral multiplicities. The Article and its Lean endpoints establish the optimal-memory side for distinct positive spectra, including rank-deficient states. The tube-volume formulas, their exact constants, and the double-scaling bridge are not included in the checked Lean theorem scope.

For arbitrary repeated positive eigenvalues, the Letter conjectures an analogous QMDL relation with a multiplicity-dependent constant; the geometric expansion alone does not prove that operational extension.

## Related

- [[Letter|Current Letter and source map]]
- [[concepts/free-entropy|Voiculescu's microstate free entropy]]
- [[definitions/physical-free-entropy-def|Physical entropy definition]]
- [[definitions/regularized-free-entropy|Regularized spectral term]]
- [[concepts/vandermonde-determinant|The volume Jacobian]]
- [[concepts/quantum-minimum-description-length|Quantum minimum description length]]
- [[open-questions/degenerate-spectrum|Repeated-eigenvalue operational extension]]
