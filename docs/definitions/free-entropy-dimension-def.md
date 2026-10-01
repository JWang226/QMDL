# Free Entropy Dimension for a Finite Spectrum

**Source:** current [[Letter]], discussion following `eq:reg_free_ent` and End Matter on degenerate spectra in [letter.tex](https://github.com/JWang226/QMDL/blob/main/letter.tex). General perturbative definitions belong to the broader free-probability background and the earlier [[Notes]].

## Atomic Spectral Formula

For a self-adjoint $d\times d$ matrix with distinct eigenvalues $p_1,\ldots,p_m$ and multiplicities $g_1,\ldots,g_m$, its normalized spectral measure is

$$\mu_\rho=\sum_{a=1}^m\frac{g_a}{d}\delta_{p_a}.$$

The single-variable free entropy dimension is

$$
\delta(\rho)=1-\sum_a\mu_\rho(\{p_a\})^2
=1-\frac{\sum_a g_a^2}{d^2}.
$$

Thus $N_\rho=d^2\delta(\rho)=d^2-\sum_a g_a^2$ is the real dimension of the unitary orbit. At fixed $d$, $0\le\delta\le1-1/d$. The lower bound is attained by scalar matrices and the upper bound by simple spectra. A zero eigenvalue has its full multiplicity in this calculation.

## Examples

| Spectrum | $\delta(\rho)$ | Real orbit dimension |
| --- | --- | --- |
| All $d$ eigenvalues distinct | $1-1/d$ | $d^2-d$ |
| Scalar matrix | $0$ | $0$ |
| Pure state | $2(d-1)/d^2$ | $2(d-1)$ |
| Normalized rank-$k$ projector, $\rho=P/k$ | $2k(d-k)/d^2$ | $2k(d-k)$ |

For the last row, the eigenvalues are $1/k$ with multiplicity $k$ and $0$ with multiplicity $d-k$. The projector $P$ itself has eigenvalues $1$ and $0$ and the same orbit dimension.

## Geometric and Operational Roles

The Letter derives the geometric formula, for arbitrary fixed multiplicities,

$$
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=d^2\delta(\rho)\log_2\varepsilon^{-1}
+\chi_{\mathrm{reg}}(\rho)+c(d,(g_a))
+O_d(\varepsilon^2/g^2).
$$

For states whose **positive** eigenvalues are distinct, [[Article|Article Theorem 1]] proves that the optimal memory cost has leading term $\tfrac12d^2\delta(\rho)\log_2n$, with the explicit additive constant. The Letter expects the analogous operational statement for arbitrary repeated positive spectra, but does not prove it. Neither the entropy definitions nor the general geometric formula are part of the current Lean theorem scope.

## Used By

- [[concepts/free-entropy-dimension|Free Entropy Dimension]]
- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[open-questions/degenerate-spectrum|QMDL for repeated positive eigenvalues]]
