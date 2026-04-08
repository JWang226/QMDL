# Free Entropy Dimension

**Appears in:** [[Letter]] (Appendix A), [[Article]]

## Intuition

Free entropy dimension measures the "effective number of continuous parameters" needed to describe an operator, normalized to $[0, 1]$. It generalizes the Minkowski dimension (or entropy dimension) to the non-commutative setting. A maximally non-degenerate operator has dimension close to 1; a scalar multiple of the identity has dimension 0.

Physically, $d^2 \cdot \delta(\rho)$ counts the real degrees of freedom in specifying a Hermitian matrix with the spectral degeneracy pattern of $\rho$. For a non-degenerate spectrum, this is $d^2 - d$ (the dimension of the unitary orbit modulo the stabilizer), and for the maximally mixed state it is 0 (no orbit at all).

## Formal Definition (Voiculescu)

$$\delta(a) = 1 + \limsup_{\varepsilon \to 0} \frac{\chi(a + \varepsilon s)}{-\log \varepsilon}$$

where $s$ is a freely independent standard semicircular element (the free probability analogue of a Gaussian). The semicircular smearing regularizes the divergences in $\chi(a)$, and the limit extracts the *degree* of the logarithmic divergence.

We always have $0 \leq \delta(a) \leq 1$, with $\delta(a) = 1$ if and only if $\chi(a) > -\infty$.

## Derivation via Semicircular Smearing (Letter, Appendix A)

The free entropy of a finite-dimensional density matrix $\rho$ diverges because its spectral measure consists of point masses. Adding a semicircular element $\varepsilon s$ smooths the spectrum: the spectral density of $\rho + \varepsilon s$ is computed via the free additive convolution, yielding a continuous density with as many disconnected domains as distinct eigenvalues, each of width $O(\varepsilon)$.

The resulting free entropy admits the small-$\varepsilon$ expansion:

$$\chi(\rho + \varepsilon s) = \frac{\sum_i g_i^2}{d^2}\log \varepsilon + \chi_{\mathrm{reg}}(\rho) + \mathrm{const} + O(\varepsilon)$$

where $g_i$ are the spectral multiplicities. Substituting into the definition:

$$\delta(\rho) = 1 + \lim_{\varepsilon \to 0}\frac{\frac{\sum_i g_i^2}{d^2}\log\varepsilon + \chi_{\mathrm{reg}}(\rho) + \mathrm{const}}{-\log\varepsilon} = 1 - \frac{\sum_i g_i^2}{d^2}$$

The $\chi_{\mathrm{reg}}$ and constant terms vanish in the limit because they are $O(1)$ relative to $\log\varepsilon$. What remains is precisely the coefficient of the logarithmic divergence.

This connects directly to the [[concepts/physical-free-entropy|Physical Free Entropy]]: the divergent piece $\frac{\sum_i g_i^2}{d^2}\log\varepsilon$ in $\chi(\rho)$ is absorbed into the universal $d^2\log(1/\varepsilon)$ term, yielding $\chi_{\mathrm{phy}}(\rho;\varepsilon) = d^2\delta(\rho)\log(1/\varepsilon) + \chi_{\mathrm{reg}}(\rho) + \mathrm{const}$.

## Explicit Formula

For a $d$-dimensional operator with spectral degeneracies $g_1, \ldots, g_m$ (where $\sum g_i = d$), the free entropy dimension is:

$$\delta(\rho) = 1 - \frac{\sum_i g_i^2}{d^2}$$

This follows from the general formula for the free entropy dimension of a single variable with atoms: $\delta(a) = 1 - \sum_{t \in \mathbb{R}} \mu_a(\{t\})^2$, where $\mu_a$ is the spectral measure. For $\rho$ with eigenvalue $p_i$ of multiplicity $g_i$, the atom at $p_i$ has mass $g_i/d$, so $\mu_\rho(\{p_i\})^2 = g_i^2/d^2$.

The unnormalized version $d^2 \cdot \delta(\rho) = d^2 - \sum_i g_i^2$ directly counts real degrees of freedom: a $d \times d$ Hermitian matrix has $d^2$ real parameters, and fixing a spectral degeneracy pattern with multiplicities $g_i$ removes $\sum_i g_i^2$ parameters (since the stabilizer subgroup $\prod_i \mathrm{U}(g_i)$ has total dimension $\sum_i g_i^2$).

## Examples

### Non-degenerate spectrum ($g_i = 1$ for all $i$)

$$\delta(\rho) = 1 - \frac{d}{d^2} = \frac{d-1}{d}$$

The unnormalized dimension is $d^2 - d = d(d-1)$, which equals the real dimension of the flag manifold $\mathrm{U}(d) / \mathrm{U}(1)^d$. This is the orbit of a Hermitian matrix with all-distinct eigenvalues.

### Maximally mixed state ($\rho = I/d$, i.e., $g_1 = d$)

$$\delta(I/d) = 1 - \frac{d^2}{d^2} = 0$$

Zero degrees of freedom: the maximally mixed state is invariant under all unitaries, so it has no eigenbasis information. Its QMDL is $0 \cdot \log n = 0$ at leading order.

### Rank-1 projector (pure state $|\psi\rangle\langle\psi|$)

Two distinct eigenvalues: $1$ with multiplicity 1, and $0$ with multiplicity $d-1$. So $g_1 = 1, g_2 = d-1$:

$$\delta(|\psi\rangle\langle\psi|) = 1 - \frac{1 + (d-1)^2}{d^2} = \frac{2(d-1)}{d^2}$$

The unnormalized dimension is $d^2 \cdot \delta = 2(d-1)$, which is the real dimension of $\mathbb{CP}^{d-1}$ -- the space of pure states. The QMDL of $|\psi\rangle\langle\psi|^{\otimes n}$ is $(d-1)\log n$ at leading order.

### Rank-$k$ projector ($P = \mathrm{diag}(\underbrace{1/k, \ldots, 1/k}_k, \underbrace{0, \ldots, 0}_{d-k})$)

Eigenvalue $1/k$ with multiplicity $k$ and eigenvalue $0$ with multiplicity $d-k$:

$$\delta(P) = 1 - \frac{k^2 + (d-k)^2}{d^2} = \frac{2k(d-k)}{d^2}$$

This is symmetric in $k \leftrightarrow d-k$ and maximized at $k = d/2$ (half-rank projector), giving $\delta = 1/2$. The unnormalized dimension $2k(d-k)$ equals the real dimension of the Grassmannian $\mathrm{Gr}(k, d)$ -- the space of $k$-dimensional subspaces of $\mathbb{C}^d$.

### Two distinct eigenvalues with multiplicities $g$ and $d-g$

$$\delta = \frac{2g(d-g)}{d^2}$$

This interpolates between $\delta = 0$ (when $g = 0$ or $g = d$, i.e., all eigenvalues equal) and $\delta_{\max} = 1/2$ (when $g = d/2$). Note this is the same formula as the rank-$k$ projector with $g = k$.

## Role in QMDL

The free entropy dimension governs the **leading-order** compression rate:

$$\log|M_n| = \frac{d^2 \cdot \delta(\rho)}{2} \log n + O(1)$$

For a non-degenerate rank-$r$ state in $\mathbb{C}^d$:

$$\frac{d^2 \cdot \delta(\rho)}{2} = \frac{r(2d - r - 1)}{2}$$

This equals the real dimension of the flag manifold $\mathrm{U}(d) / (\mathrm{U}(1)^r \times \mathrm{U}(d-r))$ divided by 2 -- reflecting the fact that the eigenbasis of a rank-$r$ non-degenerate state is parameterized by this manifold. The division by 2 is the geometric quantization factor from the [[concepts/physical-free-entropy|Kirillov-Kostant-Souriau theorem]].

## Related

- [[concepts/physical-free-entropy|Physical Free Entropy]] -- $\chi_{\mathrm{phy}} = d^2 \delta \cdot \log(1/\varepsilon) + \chi_{\mathrm{reg}} + \text{const}$
- [[concepts/free-entropy|Free Entropy]] -- parent concept
- [[definitions/regularized-free-entropy|Regularized Free Entropy]] -- the subleading $O(1)$ term
- [[concepts/vandermonde-determinant|Vandermonde Determinant]] -- the Jacobian whose structure determines $\delta$

## External References

- [Free entropy (Wikipedia)](https://en.wikipedia.org/wiki/Free_entropy)
- [Voiculescu, "The analogues of entropy and of Fisher's information measure in free probability theory, II" (1994)](https://doi.org/10.1007/BF01231539)
- [F. Hiai and D. Petz, *The Semicircle Law, Free Random Variables and Entropy*, AMS Mathematical Surveys and Monographs, vol. 77 (2000)](https://bookstore.ams.org/view?ProductCode=SURV/77)
