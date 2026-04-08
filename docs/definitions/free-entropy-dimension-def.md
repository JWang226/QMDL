# Free Entropy Dimension (Formal Definition)

**Source:** Notes line ~200; Letter Eq. 34 (line ~385)

## Statement (Voiculescu)

For a bounded self-adjoint operator $a$ in a tracial von Neumann algebra:

$$\delta(a) = 1 + \limsup_{\varepsilon \to 0} \frac{\chi(a + \varepsilon s)}{-\log \varepsilon}$$

where $s$ is a freely independent standard [[concepts/semicircular-element|Semicircular Element]].

## Statement (Finite Dimensions)

For a $d \times d$ operator with spectral measure $\mu_a = \sum_i (g_i/d) \cdot \delta_{p_i}$:

$$\delta(a) = 1 - \sum_i \mu_a(\{p_i\})^2 = 1 - \frac{\sum_i g_i^2}{d^2}$$

## Intuition

The free entropy dimension measures what fraction of the full $d^2$ degrees of freedom of a $d \times d$ Hermitian matrix are "active" for $\rho$. A generic Hermitian matrix with all distinct eigenvalues can be freely rotated by $U(d)$, giving $d^2 - d$ real orbital degrees of freedom out of $d^2$ total, so $\delta = 1 - 1/d$. When eigenvalues are degenerate, the orbit shrinks because rotations within degenerate eigenspaces are undetectable.

### Why $0 \leq \delta \leq 1$

The finite-dimensional formula $\delta(a) = 1 - \sum_i (g_i/d)^2$ is manifestly bounded. Since $\mu_a(\{p_i\}) = g_i/d$ defines a probability distribution on the distinct eigenvalues (with $\sum_i g_i/d = 1$), the sum $\sum_i (g_i/d)^2$ is the squared $\ell^2$-norm of a probability vector. By Cauchy-Schwarz (or the fact that $\|q\|_2^2 \leq \|q\|_1^2 = 1$ for any probability vector $q$):

$$0 < \sum_i \left(\frac{g_i}{d}\right)^2 \leq 1$$

The upper bound $\sum_i (g_i/d)^2 = 1$ is achieved when the spectral measure is a single point mass, i.e., $\rho = c \cdot I$ (a scalar multiple of the identity). In this case $\delta = 0$, meaning the orbit is trivial.

The lower bound $\sum_i (g_i/d)^2 = 1/d$ is achieved when all eigenvalues are distinct ($g_i = 1$ for all $i$, giving $m = d$ terms each equal to $1/d^2$). In this case $\delta = 1 - 1/d$, which approaches 1 as $d \to \infty$.

## Qubit Example ($d = 2$)

For a qubit:
- **Non-degenerate spectrum** ($p \neq 1/2$): multiplicities $g_1 = g_2 = 1$, so $\delta = 1 - (1/4 + 1/4) = 1/2$. The number of orbital degrees of freedom is $d^2 \delta = 4 \cdot 1/2 = 2$, matching the 2 real parameters of $SU(2)/U(1)$.
- **Maximally mixed** ($p = 1/2$): multiplicity $g_1 = 2$, so $\delta = 1 - 1 = 0$. The orbit is a single point (the maximally mixed state is invariant under all unitaries).

For a rank-$k$ projector in $d$ dimensions (eigenvalues $1/k$ with multiplicity $k$ and $0$ with multiplicity $d - k$):

$$\delta(P) = 1 - \left(\frac{k}{d}\right)^2 - \left(\frac{d-k}{d}\right)^2 = \frac{2k(d-k)}{d^2}$$

For a rank-1 pure state in $d$ dimensions: $\delta = 2(d-1)/d^2$, and $d^2 \delta = 2(d-1)$, which correctly counts the real dimension of $\mathbb{CP}^{d-1}$.

## Connection to Proof Architecture

The free entropy dimension controls the **leading-order** term in the [[concepts/physical-free-entropy|Physical Free Entropy]]:

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = d^2 \delta(\rho) \log(1/\varepsilon) + \chi_{\mathrm{reg}}(\rho) + \mathrm{const} + O(\varepsilon)$$

In the QMDL formula, this translates to the coefficient of $\log n$: the leading compression rate is $\frac{d^2 \delta(\rho)}{2} \log n$. The factor of $1/2$ arises from geometric quantization (the passage from the Euclidean measure on Hermitian matrices to the symplectic measure on coadjoint orbits).

## Used By

- [[concepts/free-entropy-dimension|Free Entropy Dimension]] (concept page)
- [[concepts/physical-free-entropy|Physical Free Entropy]]
