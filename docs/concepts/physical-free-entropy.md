# Physical Free Entropy

**Appears in:** [[Letter]] (Eq. 8-11, Appendix A), [[Article]]

## Intuition

Voiculescu's original free entropy is defined via a limit involving $N \times N$ random matrices as $N \to \infty$, making it divergent for finite-dimensional operators (where the spectral measure is a sum of delta functions). The **physical free entropy** is a finite-dimensional, resolution-dependent version that is always non-negative and directly relates to covering numbers.

Think of it as: "how many Hilbert-Schmidt balls of radius $\varepsilon$ do you need to cover all $d \times d$ Hermitian matrices with spectrum close to $\rho$'s spectrum?" The logarithm of this covering number is the physical free entropy.

The relationship between free entropy and physical free entropy exactly mirrors the relationship between Shannon's differential entropy $h(p)$ and the discrete Shannon entropy $H(p_\varepsilon)$ of a discretized distribution: $H(p_\varepsilon) \simeq d\log(1/\varepsilon) + h(p)$. Similarly, $\chi_{\mathrm{phy}}(\rho;\varepsilon) = d^2\delta(\rho)\log(1/\varepsilon) + \chi_{\mathrm{reg}}(\rho) + \mathrm{const}$.

## Formal Definition

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = \log \mathcal{N}(\Omega_\varepsilon, \varepsilon)$$

where:
- $\mathcal{N}(\Omega_\varepsilon, \varepsilon)$ = minimum number of Hilbert-Schmidt $\varepsilon$-balls needed to cover $\Omega_\varepsilon$
- $\Omega_\varepsilon = \{X_d \in M_d^{\mathrm{s.a.}} : \|\lambda(X_d) - p\|_2 \leq \varepsilon\}$ is the spectral neighborhood -- all Hermitian matrices whose ordered eigenvalues are within $L^2$-distance $\varepsilon$ of the spectrum $p$ of $\rho$
- Requires $\varepsilon < g/2$ where $g = \min_i |p_{i+1} - p_i|$ is the minimal spectral gap

## Full Derivation (Letter, Appendix A)

The derivation proceeds in four clean steps.

### Step 1: Eigenvalue-eigenvector coordinates and the Jacobian

Every $d \times d$ Hermitian matrix $X$ can be decomposed as $X = U \Lambda U^\dagger$ where $\Lambda = \mathrm{diag}(\lambda_1, \ldots, \lambda_d)$ with ordered eigenvalues $\lambda_1 \leq \cdots \leq \lambda_d$, and $U$ is unitary (defined up to phase ambiguities). The Lebesgue measure on $M_d^{\mathrm{s.a.}}$ in these coordinates has a Jacobian that produces the squared [[concepts/vandermonde-determinant|Vandermonde Determinant]]:

$$dX = c_d \prod_{1 \leq i < j \leq d}(\lambda_i - \lambda_j)^2 \, d\lambda_1 \cdots d\lambda_d \, d\nu(U)$$

where $c_d = \pi^{d(d-1)/2} / \prod_{k=1}^{d-1} k!$ is a normalization constant and $d\nu(U)$ is the Haar measure on the relevant quotient of $\mathrm{U}(d)$.

This is the fundamental fact: the eigenvalue repulsion factor $|\Delta(\lambda)|^2$ appears as a geometric Jacobian. Matrices with nearly-degenerate eigenvalues occupy less volume, which is why free entropy decreases for degenerate spectra.

### Step 2: Volume of the spectral neighborhood factorizes

The spectral neighborhood $\Omega_\varepsilon$ consists of all Hermitian matrices whose eigenvalues lie within an $L^2$-ball of radius $\varepsilon$ around $p$. Because the eigenvalue constraint defines a $d$-dimensional ball $D_\varepsilon = B_\varepsilon^d(p)$ and the unitary part integrates out to a constant (the orbital volume), we get:

$$\mathrm{Vol}(\Omega_\varepsilon) \simeq c_d \cdot \mathrm{Vol}(D_\varepsilon) \cdot \Delta(p)^2$$

For small $\varepsilon$, the Vandermonde factor is approximately constant over $D_\varepsilon$ and can be evaluated at $p$. The eigenvalue ball has volume $\mathrm{Vol}(D_\varepsilon) = \pi^{d/2}\varepsilon^d / \Gamma(d/2 + 1)$. Combining:

$$\mathrm{Vol}(\Omega_\varepsilon) \simeq \frac{\pi^{d(d-1)/2}}{\prod_{k=1}^{d-1} k!} \cdot \frac{\pi^{d/2}\varepsilon^d}{\Gamma(d/2+1)} \cdot \prod_{i < j}(p_i - p_j)^2$$

### Step 3: Covering number ratio -- $\pi$ factors cancel perfectly

The covering number is approximated by the volume ratio:

$$\mathcal{N}(\Omega_\varepsilon, \varepsilon) \simeq \frac{\mathrm{Vol}(\Omega_\varepsilon)}{\mathrm{Vol}(B_\varepsilon^{d^2})}$$

The reference ball $B_\varepsilon^{d^2}$ has volume $\mathrm{Vol}(B_\varepsilon^{d^2}) = \pi^{d^2/2}\varepsilon^{d^2} / \Gamma(d^2/2 + 1)$.

A beautiful cancellation occurs: the total power of $\pi$ in $\mathrm{Vol}(\Omega_\varepsilon)$ is $\pi^{d(d-1)/2 + d/2} = \pi^{d^2/2}$, which exactly matches the $\pi^{d^2/2}$ in $\mathrm{Vol}(B_\varepsilon^{d^2})$. The ratio becomes:

$$\mathcal{N}(\Omega_\varepsilon, \varepsilon) \simeq \frac{\Gamma(d^2/2+1)}{\Gamma(d/2+1)\prod_{k=1}^{d-1} k!} \cdot \varepsilon^{-(d^2-d)} \cdot \prod_{i<j}(p_i - p_j)^2$$

### Step 4: Take the logarithm to get the physical free entropy

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = (d^2 - d)\log(1/\varepsilon) + 2\sum_{i < j}\log|p_i - p_j| - \sum_{k=1}^{d-1}\log k! + \log\frac{\Gamma(d^2/2+1)}{\Gamma(d/2+1)} + O(\varepsilon)$$

This decomposes as:

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = \underbrace{d^2 \cdot \delta(\rho)}_{\text{dimension}}\log(1/\varepsilon) + \underbrace{\chi_{\mathrm{reg}}(\rho)}_{\text{eigenvalue-dependent}} + \underbrace{\text{const}}_{\text{$d$-dependent only}} + O(\varepsilon)$$

## Degenerate Spectrum Case (Letter, Appendix B)

When $\rho$ has distinct eigenvalues $p_1 < \cdots < p_m$ with multiplicities $g_1, \ldots, g_m$ ($\sum_a g_a = d$), the Vandermonde determinant splits into inter-block and intra-block contributions.

### Inter-block terms

For eigenvalues in different blocks $a$ and $b$, we have $\lambda_{b,s} - \lambda_{a,r} = (p_b - p_a) + (x_{b,s} - x_{a,r})$ where $|x_{a,r}| \leq \varepsilon$. For small $\varepsilon$, the inter-block contribution is:

$$\prod_{a < b}\prod_{r,s}(p_b - p_a + O(\varepsilon))^2 \simeq \prod_{a < b}(p_b - p_a)^{2g_a g_b}$$

### Intra-block terms

Within block $a$, eigenvalues are separated by $O(\varepsilon)$. Rescaling $\lambda_{a,r} = p_a + \varepsilon \cdot y_{a,r}$, the intra-block Vandermonde contributes:

$$\prod_a \varepsilon^{g_a(g_a - 1)} \cdot W(y)$$

where $W(y) = \prod_a \prod_{r < s}(y_{a,s} - y_{a,r})^2$ absorbs into a geometric constant upon integration.

### Result

The total volume picks up an extra $\varepsilon^{\sum_a g_a^2}$ factor (compared to $\varepsilon^d$ from the non-degenerate case), and the physical free entropy becomes:

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = \left(d^2 - \sum_a g_a^2\right)\log(1/\varepsilon) + 2\sum_{a < b}g_a g_b \log|p_a - p_b| + \mathrm{const} + O(\varepsilon)$$

This reduces to the non-degenerate formula when all $g_a = 1$. The coefficient $d^2 - \sum_a g_a^2$ counts the true number of real degrees of freedom for a Hermitian matrix with the given spectral degeneracy pattern.

### Rank-deficient case

For rank-$r$ states ($r < d$) with non-degenerate nonzero eigenvalues, the degeneracies are $g_0 = d - r$ (for eigenvalue 0) and $g_{i \geq 1} = 1$:

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = r(2d - r - 1)\log(1/\varepsilon) + 2\sum_{1 \leq i < j}\log|p_i - p_j| + 2(d-r)\sum_{i \geq 1}\log p_i + \mathrm{const}$$

For a pure state ($r = 1$): $\chi_{\mathrm{phy}}(|\psi\rangle\langle\psi|; \varepsilon) = (2d-2)\log(1/\varepsilon) + \mathrm{const}$, giving QMDL of $(d-1)\log n$ -- matching the dimension of the symmetric subspace.

## Connection to QMDL

The central result of the project:

$$\log|M_n| = \frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1/2}) + \text{universal constant} + o(1)$$

The factor of $1/2$ reflects the passage from continuous geometry (Lebesgue measure on Hermitian matrices, with squared Vandermonde $\Delta(p)^2$) to discrete quantum (Weyl dimension formula, with first-power Vandermonde $\Delta(p)$). This is precisely the signature of geometric quantization via the Kirillov-Kostant-Souriau theorem: the symplectic form pairs the $d(d-1)$ real orbital dimensions into $d(d-1)/2$ canonically conjugate variables.

## Related

- [[concepts/free-entropy|Free Entropy]] -- Voiculescu's original infinite-dimensional definition
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- the leading $\log(1/\varepsilon)$ coefficient $\delta(\rho)$
- [[definitions/regularized-free-entropy|Regularized Free Entropy]] -- the $O(1)$ correction $\chi_{\mathrm{reg}}(\rho)$
- [[concepts/vandermonde-determinant|Vandermonde Determinant]] -- appears as the Jacobian in Step 1
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- the operational interpretation
