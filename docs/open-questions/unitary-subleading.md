# Open: Subleading Term for Unitary Programming

**Source:** Notes, line ~1476 (JW comment)
**Status:** Open

## Context

For state compression, the subleading $O(1)$ term is precisely the [[definitions/regularized-free-entropy|Regularized Free Entropy]] $\chi_{\mathrm{reg}}(\rho)$, which equals $\frac{2}{d^2}\sum_{i<j} \log |p_i - p_j|$ -- a sum of log-distances between eigenvalues. For unitary programming, only the leading-order term $\frac{f}{2}\log(1/\varepsilon)$ is established (Notes, line ~1476).

## Question

What is the $O(1)$ subleading term for the unitary programming rate? The authors conjecture it involves the **Kirillov character formula** for the relevant Lie group.

## The Kirillov Character Formula

The Kirillov character formula is a deep result in representation theory that expresses the **character** of an irreducible representation $H_\lambda$ as an integral over the coadjoint orbit $\mathcal{O}_\lambda$:

$$\chi_\lambda(\exp X) = \frac{1}{j(X)} \int_{\mathcal{O}_\lambda} e^{i \langle \xi, X \rangle} \, d\mu_\lambda(\xi)$$

where $j(X)$ is a universal factor (the square root of the determinant of the Jacobian of the exponential map) and $d\mu_\lambda$ is the Liouville measure on the orbit.

### Why It Might Give the $O(1)$ Term

The connection to the subleading term comes through the following reasoning:

1. The **leading order** of $\dim H_\lambda$ equals the symplectic volume of $\mathcal{O}_\lambda$ (this is the [[concepts/kks-theorem|KKS Theorem]] content, giving the $\frac{f}{2}\log(1/\varepsilon)$ term).

2. The **subleading corrections** to $\dim H_\lambda$ come from the $O(1)$ terms in the asymptotic expansion of the Weyl dimension formula. These corrections involve the Weyl vector $\rho_W$ and the denominators of the Weyl character formula.

3. The Kirillov character formula provides a geometric way to compute these corrections: they arise from the curvature of the coadjoint orbit and the correction factor $j(X)$. In the unitary case (orbits in $\mathfrak{u}(d)^*$), these corrections should give the free entropy $\chi_{\mathrm{reg}}(u) = \frac{2}{d^2}\sum_{i<j} \log|z_i - z_j|$ evaluated on the eigenvalues $z_i$ of the unitary.

Establishing this rigorously would complete the parallel between state compression (where the $O(1)$ term is $\chi_{\mathrm{reg}}(\rho)$) and unitary programming (where it should be $\chi_{\mathrm{reg}}(u)$).

## Related

- [[concepts/unitary-programming|Unitary Programming]]
- [[definitions/regularized-free-entropy|Regularized Free Entropy]]
- [[concepts/free-entropy|Free Entropy]]
