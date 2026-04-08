# Physical Free Entropy (Formal Definition)

**Label:** `eq:free_phys_def` (Letter)
**Source:** Letter Eq. 8 (line ~149); Notes line ~153

## Statement

For a $d \times d$ density matrix $\rho$ with minimal spectral gap $g = \min_{i \neq j}|p_i - p_j|$, and for $\varepsilon < g/2$, the **physical free entropy** is:

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = \log N(\Omega_\varepsilon, \varepsilon)$$

where:
- $\Omega_\varepsilon = \{X \in M_d^{\mathrm{s.a.}} : \|{\mathrm{spec}(X) - \mathrm{spec}(\rho)}\|_2 \leq \varepsilon \}$ is the set of Hermitian matrices whose spectrum is $\varepsilon$-close (in $L^2$) to that of $\rho$
- $N(\Omega, \varepsilon)$ is the minimum number of Hilbert-Schmidt $\varepsilon$-balls needed to cover $\Omega$

## Intuition

How many "patches" of size $\varepsilon$ do you need to cover all Hermitian matrices that look spectrally similar to $\rho$? The answer is dominated by the volume of the unitary orbit, which depends on eigenvalue spacings through the [[concepts/vandermonde-determinant|Vandermonde Determinant]].

### Why $\varepsilon < g/2$

The constraint $\varepsilon < g/2$ (where $g = \min_{i \neq j}|p_i - p_j|$ is the minimal spectral gap) is essential for the covering number to be well-defined and meaningful. Here is the geometric reason:

When $\varepsilon < g/2$, any matrix $X \in \Omega_\varepsilon$ has eigenvalues that remain in *separated clusters* around each $p_i$. Specifically, the eigenvalue closest to $p_i$ stays within distance $\varepsilon < g/2$ of $p_i$, so it cannot approach any other $p_j$. This means:

1. **The eigenvalue labeling is stable:** We can unambiguously associate each eigenvalue of $X$ with a specific $p_i$. The ordering of eigenvalues is preserved.
2. **The orbit topology is fixed:** The unitary orbit of any $X \in \Omega_\varepsilon$ has the same topology as that of $\rho$ (namely $U(d)/\prod_a U(g_a)$, where $g_a$ are the multiplicities). No eigenvalue crossings can occur.
3. **The Vandermonde determinant stays controlled:** Since eigenvalues cannot collide, the squared Vandermonde $\prod_{i<j}(\lambda_i - \lambda_j)^2$ stays close to $\prod_{i<j}(p_i - p_j)^2$, justifying the approximation used in the volume calculation.

If $\varepsilon \geq g/2$, eigenvalues from different clusters could merge. This would change the dimension of the unitary orbit (e.g., from $d^2 - d$ to $d^2 - \sum g_a^2$ for a coarser degeneracy pattern), making the covering number discontinuous.

## Worked Example: Qubit ($d = 2$)

For a qubit with eigenvalues $p_1 = 0.7$, $p_2 = 0.3$, at resolution $\varepsilon = 0.1$:

- Spectral gap: $g = |0.7 - 0.3| = 0.4$, so we need $\varepsilon < 0.2$. Our choice $\varepsilon = 0.1$ satisfies this.
- Degrees of freedom: $d^2 - d = 4 - 2 = 2$ (one complex off-diagonal parameter).
- The physical free entropy is:

$$\chi_{\mathrm{phy}}(\rho; 0.1) = (4 - 2)\log(1/0.1) + 2\log|0.7 - 0.3| + \mathrm{const}$$

$$= 2\log 10 + 2\log 0.4 + \mathrm{const} \approx 6.64 - 2.64 + \mathrm{const} \approx 4.0 + \mathrm{const}$$

(using $\log_2$). So there are roughly $2^4 = 16$ distinguishable density matrices with spectrum close to $(0.7, 0.3)$ at resolution $\varepsilon = 0.1$. Note how the Vandermonde term $2\log(0.4)$ reduces the count: matrices with more separated eigenvalues fill out a larger orbit, but the logarithmic potential is still negative because $|p_1 - p_2| < 1$.

## Connection to Proof Architecture

The physical free entropy is the bridge between the mathematical free entropy (which diverges in finite dimensions) and the operationally meaningful QMDL. The main result of the Letter establishes:

$$|M| = \frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1}) + \mathrm{const} + o(1)$$

The factor of $1/2$ reflects geometric quantization: Voiculescu's free entropy counts with the flat Euclidean (Lebesgue) measure, yielding a squared Vandermonde $\Delta(p)^2$, while the QMDL counts quantum states via the Weyl dimension formula, which involves only the first power $\Delta(p)$ due to the symplectic structure of coadjoint orbits.

## Used By

- [[concepts/physical-free-entropy|Physical Free Entropy]] (concept page)
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
