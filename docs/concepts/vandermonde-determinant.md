# Vandermonde Determinant

**Appears in:** [[Letter]] (Appendix A), [[Article]]

## Definition

For scalars $x_1, \ldots, x_d$:

$$\Delta(x) = \prod_{1 \leq i < j \leq d} (x_i - x_j) = \det \begin{pmatrix} 1 & 1 & \cdots & 1 \\ x_1 & x_2 & \cdots & x_d \\ \vdots & & & \vdots \\ x_1^{d-1} & x_2^{d-1} & \cdots & x_d^{d-1} \end{pmatrix}$$

The Vandermonde determinant vanishes if and only if two of the $x_i$ coincide, and its magnitude measures how "spread out" the values are.

## Role in Free Entropy

The Vandermonde determinant is the bridge between random matrix theory and free entropy. It appears in three interconnected roles:

### 1. The Jacobian of eigenvalue-eigenvector decomposition

Every $d \times d$ Hermitian matrix $X = U\Lambda U^\dagger$ can be parameterized by its ordered eigenvalues $\lambda_1 \leq \cdots \leq \lambda_d$ and a unitary $U$ (modulo phases). The Lebesgue measure on the $d^2$-dimensional space of Hermitian matrices transforms as:

$$dX = c_d \prod_{i < j}(\lambda_i - \lambda_j)^2\, d\lambda_1 \cdots d\lambda_d \, d\nu(U) = c_d \, |\Delta(\lambda)|^2 \, d\lambda \, d\nu(U)$$

where $c_d = \pi^{d(d-1)/2}/\prod_{k=1}^{d-1} k!$ and $d\nu(U)$ is the Haar measure on the relevant quotient. The squared Vandermonde $|\Delta(\lambda)|^2$ is the Jacobian of the change of coordinates. This is the fundamental fact underlying everything: the flat Euclidean measure on Hermitian matrices, when written in spectral coordinates, acquires a density proportional to $|\Delta(\lambda)|^2$.

### 2. Eigenvalue repulsion

The factor $|\Delta(\lambda)|^2$ in the measure explains why eigenvalues of random Hermitian matrices *repel*: configurations with nearly-degenerate eigenvalues contribute exponentially less volume. If $\lambda_i \approx \lambda_j$, the factor $(\lambda_i - \lambda_j)^2$ suppresses the measure near that configuration.

For the GUE (Gaussian Unitary Ensemble), the joint eigenvalue density is:

$$p(\lambda_1, \ldots, \lambda_d) \propto |\Delta(\lambda)|^2 \cdot e^{-\frac{d}{2}\sum_i \lambda_i^2}$$

The repulsion is entirely captured by $|\Delta(\lambda)|^2$; the Gaussian factor comes from the particular choice of matrix distribution, but the Vandermonde appears universally for *any* unitarily-invariant ensemble.

This repulsion is the geometric reason that [[concepts/free-entropy|Free Entropy]] decreases for degenerate spectra: matrices with degenerate eigenvalues occupy a lower-dimensional submanifold that has zero volume in the ambient Lebesgue measure.

### 3. The free entropy formula

The regularized free entropy is the logarithm of the squared Vandermonde evaluated at the spectrum:

$$\chi_{\mathrm{reg}}(\rho) = 2\sum_{i<j}\log|p_i - p_j| = \log|\Delta(p)|^2$$

This arises directly from the covering number computation in the [[concepts/physical-free-entropy|Physical Free Entropy]] derivation: the volume of the spectral neighborhood $\Omega_\varepsilon$ is dominated by $|\Delta(p)|^2$, and after dividing by the reference ball volume and taking the log, this becomes the state-dependent part of $\chi_{\mathrm{phy}}$.

## The Covering Number Computation (Letter, Appendix A)

The Vandermonde determinant plays a starring role in the derivation of the physical free entropy formula. Here is how:

1. **Volume of $\Omega_\varepsilon$**: The spectral neighborhood is parameterized by eigenvalues in a ball $D_\varepsilon$ around $p$ and unitaries. The volume integral factorizes:

$$\mathrm{Vol}(\Omega_\varepsilon) \simeq c_d \cdot |\Delta(p)|^2 \cdot \mathrm{Vol}(D_\varepsilon)$$

The Vandermonde is approximately constant over the small eigenvalue ball and can be pulled outside the integral.

2. **Division by reference ball**: The covering number $\mathcal{N} \simeq \mathrm{Vol}(\Omega_\varepsilon)/\mathrm{Vol}(B_\varepsilon^{d^2})$. The $\varepsilon$-dependent powers give $\varepsilon^d / \varepsilon^{d^2} = \varepsilon^{-(d^2-d)}$, and the $\pi$-dependent factors cancel exactly ($\pi^{d^2/2}$ in numerator and denominator).

3. **Taking the logarithm**: $\log \mathcal{N} = (d^2-d)\log(1/\varepsilon) + \log|\Delta(p)|^2 + \mathrm{const}$, giving the physical free entropy with the Vandermonde as the state-dependent term.

For **degenerate spectra**, the Vandermonde splits into inter-block and intra-block parts. The inter-block part $\prod_{a<b}(p_b - p_a)^{2g_a g_b}$ contributes to $\chi_{\mathrm{reg}}$, while the intra-block part $\prod_a \prod_{r<s}(\lambda_{a,s} - \lambda_{a,r})^2$ produces additional powers of $\varepsilon$ that reduce the effective dimension from $d^2 - d$ to $d^2 - \sum_a g_a^2$.

## Connection to the Weyl Dimension Formula

The Weyl dimension formula for the irrep $V_\lambda$ of $\mathrm{GL}(d)$ is:

$$\dim V_\lambda = \frac{\prod_{1 \leq i < j \leq d}(\lambda_i - \lambda_j + j - i)}{\prod_{1 \leq i < j \leq d}(j - i)} = \frac{\Delta(\lambda + \rho_W)}{\Delta(\rho_W)}$$

where $\rho_W = (d-1, d-2, \ldots, 1, 0)$ is the Weyl vector. The numerator is a *generalized Vandermonde* -- the Vandermonde determinant evaluated at the shifted weights $\lambda_i + d - i$ -- and the denominator is the ordinary Vandermonde at the Weyl vector, which equals $\prod_{k=1}^{d-1} k!$.

This is not a coincidence: the Weyl dimension formula computes the symplectic volume of the coadjoint orbit associated to $\lambda$ (by the Kirillov-Kostant-Souriau theorem), and this symplectic volume is the square root of the Riemannian volume that involves $|\Delta|^2$. The factor-of-2 relationship between the physical free entropy (which involves $|\Delta(p)|^2$, the Riemannian/Euclidean volume) and the QMDL (which involves $\Delta(\lambda + \rho_W)$, the symplectic/quantum dimension) is the geometric quantization origin of the $1/2$ in $|M| = \frac{1}{2}\chi_{\mathrm{phy}} + \mathrm{const}$.

More explicitly, for typical Schur sectors $\lambda_i \approx np_i$:

$$\log \dim V_\lambda \approx \frac{d(d-1)}{2}\log n + \sum_{i<j}\log(p_i - p_j) - \sum_{k=1}^{d-1}\log k! + o(1)$$

The coefficient of $\log n$ is $d(d-1)/2 = (d^2-d)/2$, which is exactly half of the coefficient $(d^2-d)$ in the physical free entropy. The Vandermonde appears with *first* power in the Weyl formula but *squared* in the Euclidean volume -- this is the quantization halving.

## Schur Polynomials

The Schur polynomial is defined as a ratio of a generalized Vandermonde to the ordinary Vandermonde:

$$s_\lambda(x) = \frac{\det[x_j^{\lambda_i + d - i}]}{\Delta(x)}$$

This is well-defined despite the Vandermonde in the denominator, because the numerator also vanishes when any $x_i = x_j$ (being a determinant of a matrix with two equal rows). The Schur polynomial gives the character of the irrep $V_\lambda$ and satisfies $\dim V_\lambda = s_\lambda(1, 1, \ldots, 1) = \Delta(\lambda + \rho_W)/\Delta(\rho_W)$.

## Related

- [[concepts/free-entropy|Free Entropy]] -- $\chi_{\mathrm{reg}} = \log|\Delta(p)|^2$
- [[concepts/physical-free-entropy|Physical Free Entropy]] -- derived via the covering number computation using $|\Delta|^2$
- [[definitions/regularized-free-entropy|Regularized Free Entropy]] -- the finite part of free entropy
- [[concepts/schur-polynomials|Schur Polynomials]] -- ratio of generalized to ordinary Vandermonde
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] -- numerator is a generalized Vandermonde
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- the degenerate-spectrum Vandermonde splitting determines $\delta$

## External References

- [Vandermonde matrix (Wikipedia)](https://en.wikipedia.org/wiki/Vandermonde_matrix)
- [Vandermonde's identity / determinant (Wikipedia)](https://en.wikipedia.org/wiki/Vandermonde%27s_identity)
- M. L. Mehta, *Random Matrices*, 3rd edition, Academic Press (2004)
