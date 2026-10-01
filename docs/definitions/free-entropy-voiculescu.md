# Free Entropy (Voiculescu's Definition)

**Source:** current [[Letter]], `eq:free_ent` and `eq:free_ent_formula` in [letter.tex](https://github.com/JWang226/QMDL/blob/main/letter.tex). The formulas below follow its binary-logarithm and Hilbert–Schmidt Lebesgue-volume conventions.

## Statement

For a bounded self-adjoint variable $a$ in a tracial von Neumann algebra $(A,\tau)$, fix an operator-norm cutoff $R>\|a\|$ and define

$$
\Gamma_R(a;m,\varepsilon,N)=\left\{
X\in M_N^{\mathrm{s.a.}}:
\|X\|\le R,\quad
\left|N^{-1}\operatorname{Tr}X^k-\tau(a^k)\right|\le\varepsilon
\text{ for }1\le k\le m\right\}.
$$

Then

$$
\chi(a)=\inf_m\inf_{\varepsilon>0}\limsup_{N\to\infty}
\left[\frac12\log_2 N
+\frac1{N^2}\log_2\operatorname{Vol}\Gamma_R(a;m,\varepsilon,N)\right].
$$

For the stated cutoff range the result is independent of $R$. The $N^{-2}$ factor normalizes by the real dimension of the Hermitian matrix space, and $\tfrac12\log_2N$ removes the universal volume divergence. A Gaussian reference measure would define a related free-energy functional with an extra quadratic-moment term; it is not the volume convention used here.

## Single-Variable Logarithmic Energy

Writing $\mu_a$ for the spectral measure,

$$
\chi(a)=\iint\log_2|s-t|\,d\mu_a(s)\,d\mu_a(t)
+\frac34\log_2e+\frac12\log_2(2\pi).
$$

The Vandermonde factor in matrix volume gives the logarithmic interaction. Its diagonal self-interactions must not be discarded when evaluating this formula.

In particular, every finite-dimensional Hermitian matrix has atomic spectral measure

$$\mu_\rho=\frac1d\sum_{i=1}^d\delta_{p_i},$$

and hence $\chi(\rho)=-\infty$, even if all matrix eigenvalues are distinct. A finite sum of pairwise gaps is instead the [[definitions/regularized-free-entropy|regularized quantity]]; it is not Voiculescu's $\chi$ of that matrix.

## Relation to the Letter

The Letter defines [[definitions/physical-free-entropy-def|physical free entropy]] at finite dimension and resolution. Its End Matter, `rem:bridge` and `eq:bridge`, gives a conditional double-scaling recovery of $\chi$ for regular quantile discretizations with convergent logarithmic energies. That bridge is a current manuscript result, not an entirely open question. It is not part of the Article's Lean endpoints.

## Used By

- [[concepts/free-entropy|Free Entropy]]
- [[definitions/physical-free-entropy-def|Physical Free Entropy]]
- [[definitions/regularized-free-entropy|Regularized Free Entropy]]
- [[open-questions/free-entropy-conjecture|Broader operational conjectures]]
