# Free Entropy

**Appears in:** [[Letter]], [[Article]]

## Intuition

Free entropy is Voiculescu's non-commutative generalization of Shannon's differential entropy. While von Neumann entropy counts how many qubits you need to store a quantum state (preserving its entanglement with a reference), free entropy counts how many qubits you need to **describe** a quantum state -- to record its eigenbasis -- given that you already know its spectrum.

The key analogy:

| Shannon entropy | Free entropy |
|---|---|
| Counts typical *strings* | Counts typical *matrices* |
| Microstates are length-$N$ sequences $x^N$ | Microstates are $N \times N$ matrices $X_N$ |
| Typicality = empirical frequency $\approx p$ | Typicality = empirical spectrum $\approx \mu_a$ |
| Volume measured by counting | Volume measured by Lebesgue measure on $\mathbb{R}^{N^2}$ |

Shannon entropy is $\log W$ where $W$ is the number of typical strings. Free entropy is $\log W$ where $W$ is the volume of typical matrices -- those whose spectral moments approximate a given operator.

## Formal Definition

For a bounded self-adjoint operator $a$ in a tracial von Neumann algebra $(\mathcal{A}, \tau)$, Voiculescu defined:

$$\chi(a) = \inf_{m, \varepsilon} \limsup_{N \to \infty} \left[ \frac{1}{2}\log N + \frac{1}{N^2} \log \mathrm{Vol}\left(\Gamma(a; m, \varepsilon, N)\right) \right]$$

where $\Gamma(a; m, \varepsilon, N) = \{X_N \in M_N^{\mathrm{s.a.}}(\mathbb{C}) : |N^{-1}\mathrm{Tr}\, X_N^k - \tau(a^k)| \leq \varepsilon,\; \forall k \leq m\}$ is the set of $N \times N$ self-adjoint matrices whose first $m$ moments approximate those of $a$ within $\varepsilon$.

The normalization $1/N^2$ accounts for the $O(N^2)$ degrees of freedom in a Hermitian matrix. The additive $\frac{1}{2}\log N$ term removes a universal divergence in the volume.

## Closed-Form Formula

Just as Shannon's differential entropy has the closed form $h(p) = -\int p(x)\log p(x)\,dx$, the free entropy has:

$$\chi(a) = \iint_{\mathbb{R}^2} \log|x - y|\, d\mu_a(x)\, d\mu_a(y) + \frac{3}{4} + \frac{1}{2}\log 2\pi$$

where $\mu_a$ is the spectral measure of $a$. The logarithmic potential $\iint \log|x-y|$ arises because the volume of the unitary orbit of a matrix with given spectrum is controlled by the [[concepts/vandermonde-determinant|Vandermonde Determinant]].

### Finite-dimensional density matrix

For a $d$-dimensional density matrix $\rho$ with eigenvalues $p_1, \ldots, p_d$, the spectral measure is $\mu_\rho = \frac{1}{d}\sum_i \delta(x - p_i)$. Substituting into the formula gives:

$$\chi(\rho) = \frac{2}{d^2}\sum_{i < j} \log|p_i - p_j| - \infty$$

The divergence arises because delta functions collide (point masses in the double integral produce $\log 0$ terms). This is why the raw free entropy is not directly useful in finite dimensions, motivating the [[concepts/physical-free-entropy|Physical Free Entropy]] as a regularized, non-negative version.

## Worked Examples

### Qubit ($d = 2$)

Let $\rho$ have eigenvalues $(p, 1-p)$ with $0 < p < 1$ and $p \neq 1/2$. The regularized free entropy (the finite part, discarding the divergence) is:

$$\chi_{\mathrm{reg}}(\rho) = 2\log|2p - 1|$$

The physical free entropy at resolution $\varepsilon$ is:

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = 2\log(1/\varepsilon) + 2\log|2p - 1| + \mathrm{const} + O(\varepsilon)$$

Here $d^2 - d = 2$, reflecting 2 real degrees of freedom in the eigenbasis (a point on the Bloch sphere, modulo the phase). As $p \to 1/2$ (maximally mixed), the logarithmic potential diverges to $-\infty$, reflecting the fact that the maximally mixed state has no eigenbasis to describe (every basis works equally well, but the unitary orbit degenerates).

### Qutrit ($d = 3$) with spectrum $(p_1, p_2, p_3)$

For a qutrit with non-degenerate spectrum $p_1 > p_2 > p_3 > 0$:

$$\chi_{\mathrm{reg}}(\rho) = 2[\log|p_1 - p_2| + \log|p_1 - p_3| + \log|p_2 - p_3|]$$

The physical free entropy is:

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = 6\log(1/\varepsilon) + 2\log[(p_1 - p_2)(p_1 - p_3)(p_2 - p_3)] + \mathrm{const} + O(\varepsilon)$$

The coefficient 6 = $3^2 - 3$ counts the 6 real degrees of freedom in a $3 \times 3$ unitary modulo the stabilizer of a non-degenerate diagonal matrix. For the QMDL, $\varepsilon = n^{-1/2}$ and the memory cost is $\frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1/2}) + \mathrm{const}$, giving a leading term of $3\log n$.

### Maximally mixed qutrit: $\rho = I/3$

All eigenvalues are equal: $p_1 = p_2 = p_3 = 1/3$. The logarithmic potential is $-\infty$ (all gaps vanish), and the free entropy dimension is $\delta = 0$. The physical free entropy is zero (at leading order), reflecting that the maximally mixed state requires no description at all -- it has no eigenbasis information.

## Role in the Project

This is **the** central object. The main result of the project is:

$$|M| = \frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1/2}) + \mathrm{const} + o(1)$$

Free entropy gives the quantum minimum description length its second-order correction, just as Shannon entropy gives the Schumacher compression rate. The leading term $\frac{d^2 - d}{2}\log n$ is universal (depends only on dimension and rank), while the second-order term $\sum_{i<j}\log|p_i - p_j|$ is state-dependent and is precisely the regularized free entropy.

## Why "Free"?

"Free" refers to **free probability theory** (Voiculescu), where "freeness" replaces classical independence. Just as independent random variables have additive Shannon entropy, **freely independent** random variables have additive free entropy. Free entropy is extensive under free products, while von Neumann entropy is extensive under tensor products.

The relevant independence here is between eigenvalues and eigenvectors. When the eigenbasis is Haar-random (as it is for a "typical" density matrix drawn from the unitary orbit), the eigenvalues and eigenvectors become freely independent in the large-$d$ limit. This is the random matrix manifestation of freeness: the empirical spectral measure of a Haar-rotated diagonal matrix converges to a free convolution, not a classical convolution.

In physics, freeness pertains to the independence between observables separated across *time* under chaotic dynamics, whereas tensor independence pertains to observables separated across *space*. This suggests that free entropy and related quantities have a natural role in characterizing quantum information in dynamical settings.

## Related

- [[concepts/physical-free-entropy|Physical Free Entropy]] -- finite-dimensional, non-negative version
- [[definitions/regularized-free-entropy|Regularized Free Entropy]] -- the $O(1)$ eigenvalue-dependent part
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- the leading-order scaling
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- the operational task
- [[concepts/vandermonde-determinant|Vandermonde Determinant]] -- appears as $|\Delta(p)|^2$ in the volume integral
- [[concepts/free-probability-theory|Free Probability Theory]] -- the broader mathematical framework
- [[concepts/schumacher-compression|Schumacher Compression]] -- the von Neumann entropy analogue

## External References

- [Free probability (Wikipedia)](https://en.wikipedia.org/wiki/Free_probability)
- [Free entropy (Wikipedia)](https://en.wikipedia.org/wiki/Free_entropy)
- [Voiculescu, "Free entropy" (survey, 2002)](https://doi.org/10.1112/S0024609301008992)
- [F. Hiai and D. Petz, *The Semicircle Law, Free Random Variables and Entropy*, AMS Mathematical Surveys and Monographs, vol. 77 (2000)](https://bookstore.ams.org/view?ProductCode=SURV/77)
