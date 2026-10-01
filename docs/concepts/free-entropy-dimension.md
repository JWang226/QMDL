# Free Entropy Dimension

**Appears in:** [[Letter]] (physical free entropy and the End Matter's degenerate-spectrum calculation).

## Orbit Dimension

For a self-adjoint $d\times d$ matrix whose distinct eigenvalues have multiplicities $g_1,\ldots,g_m$, the unitary orbit is

$$\mathcal O_\rho\cong U(d)\big/\prod_a U(g_a),
\qquad N_\rho=\dim_{\mathbb R}\mathcal O_\rho=d^2-\sum_a g_a^2.$$

The normalized spectral measure assigns mass $g_a/d$ to the $a$th distinct eigenvalue. The Letter identifies the single-variable free entropy dimension of this atomic measure as

$$\delta(\rho)=1-\sum_a(g_a/d)^2=\frac{N_\rho}{d^2}.$$

It counts the proportion of matrix coordinates that can change along the fixed-spectrum orbit. It depends on spectral multiplicities, not on what an observer knows about the matrix.

## Role in Physical Free Entropy

The current Letter derives its small-resolution expansion by integrating the squared Vandermonde in eigenvalue coordinates. Coincident eigenvalues contribute intra-block Vandermonde factors; rescaling the eigenvalue neighborhood yields a tube volume proportional to $\varepsilon^{\sum_a g_a^2}$. Dividing by an ambient $d^2$-dimensional ball produces

$$\chi_{\mathrm{phy}}(\rho;\varepsilon)
=d^2\delta(\rho)\log\varepsilon^{-1}
+\chi_{\mathrm{reg}}(\rho)+C(d,(g_a))+O_d(\varepsilon^2/g^2).$$

Here $g$ is the smallest gap between distinct eigenvalues, with $g=\infty$ for a scalar matrix. See the source labels `eq:free_phys` and `eq:degenerate_free_ent`. The current derivation does not use semicircular smearing. The geometric expansion and its identification with free entropy dimension are manuscript results, not Lean conclusions.

## Examples

| Spectrum | Real orbit dimension $N_\rho$ | $\delta(\rho)$ |
|---|---:|---:|
| All $d$ eigenvalues distinct | $d^2-d$ | $1-1/d$ |
| Scalar matrix, including $I/d$ | $0$ | $0$ |
| Pure state | $2(d-1)$ | $2(d-1)/d^2$ |
| $k^{-1}P$ for a rank-$k$ orthogonal projector | $2k(d-k)$ | $2k(d-k)/d^2$ |

The last family has a Grassmannian orbit for $1\le k<d$. A normalized projector $k^{-1}P$ is a density operator; it is not itself an orthogonal projector unless $k=1$.

## Role in QMDL

For the Article's proved class of states—rank $r$ with distinct positive eigenvalues and zero eigenvalue of multiplicity $d-r$—

$$N_\rho=r(2d-r-1),\qquad
|M_n|=\frac{N_\rho}{2}\log n+O(1),$$

where $|M_n|=\log_2\dim M_n$. The Article and its Lean formalization determine the entire additive constant as well; see [[concepts/quantum-minimum-description-length]]. The pure-state instance has cost $(d-1)\log n-\log(d-1)!+o(1)$, while a known scalar state requires no memory.

For repeated positive eigenvalues, the orbit-dimension formula and the Letter's volume calculation still apply. The Letter's closing extension of the optimal QMDL formula to arbitrary multiplicities is a conjecture, not a consequence of the current Lean endpoint. See [[open-questions/degenerate-spectrum]].

## Related

- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[concepts/free-entropy|Free Entropy]]
- [[definitions/regularized-free-entropy|Regularized Free Entropy]]
- [[concepts/flag-manifold|Flag Manifold]]
- [[proof-structure]]

## References

- `voiculescu2002free`: Voiculescu, "Free entropy" (survey, 2002).
- `hiai2000semicircle`: Hiai and Petz, *The Semicircle Law, Free Random Variables and Entropy*.
