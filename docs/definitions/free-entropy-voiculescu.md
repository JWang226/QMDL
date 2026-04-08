# Free Entropy (Voiculescu's Definition)

**Source:** Letter Eq. 3 (line ~118); Notes line ~99

## Statement

For a bounded self-adjoint operator $a$ in a tracial von Neumann algebra $(A, \tau)$, define the **microstate space**:

$$\Gamma(a; m, \varepsilon, N) = \left\{ X \in M_N^{\mathrm{s.a.}} : \left|\mathrm{tr}_N(X^k) - \tau(a^k)\right| < \varepsilon \text{ for } k = 1, \ldots, m \right\}$$

where $M_N^{\mathrm{s.a.}}$ is the set of $N \times N$ self-adjoint matrices and $\mathrm{tr}_N = \frac{1}{N}\mathrm{Tr}$ is the normalized trace.

The **free entropy** is:

$$\chi(a) = \inf_{m \in \mathbb{N}, \varepsilon > 0} \limsup_{N \to \infty} \left[ \frac{N^2}{2}\log(2\pi e) + \frac{1}{N^2}\log \mathrm{Vol}(\Gamma(a; m, \varepsilon, N)) \right]$$

where $\mathrm{Vol}$ is the Lebesgue measure on self-adjoint matrices.

## Intuition

Count the volume of $N \times N$ matrices whose moments approximate those of $a$, renormalize by $N^2$ (the number of real parameters), and take $N \to \infty$. This is the random matrix analogue of Shannon's typical set: instead of typical sequences, we have "typical matrices."

## Explicit Formula for Finite Dimensions

For a $d \times d$ density matrix $\rho$ with eigenvalues $p_1, \ldots, p_d$:

$$\chi(\rho) = \sum_{i < j} \log|p_i - p_j|^2 + \frac{d}{2}\log(2\pi e) + \frac{d(d-1)}{4}\log 2$$

The eigenvalue-dependent part is $2\sum_{i<j}\log|p_i - p_j|$, the log squared [[concepts/vandermonde-determinant|Vandermonde Determinant]].

### Understanding the $N^2/2$ normalization

The normalization in the definition arises from the geometry of the space of $N \times N$ self-adjoint matrices:

1. **Counting real parameters:** An $N \times N$ self-adjoint (Hermitian) matrix has $N$ real diagonal entries and $N(N-1)/2$ complex off-diagonal entries (each contributing 2 real parameters). Total: $N + N(N-1) = N^2$ real parameters. So $M_N^{\mathrm{s.a.}}$ embeds into $\mathbb{R}^{N^2}$.

2. **The Gaussian reference measure:** If we draw a random $N \times N$ GUE matrix, the probability density is proportional to $\exp(-N \cdot \mathrm{Tr}(X^2)/2)$. Integrating this Gaussian over $\mathbb{R}^{N^2}$ gives a volume factor of $(2\pi/N)^{N^2/2}$, contributing $\frac{N^2}{2}\log(2\pi/N)$ to the log-volume. After appropriate normalization, the term $\frac{N^2}{2}\log(2\pi e)$ exactly cancels this reference Gaussian contribution, isolating the non-trivial information about the spectral distribution of $a$.

3. **Per degree of freedom:** Dividing $\log \mathrm{Vol}$ by $N^2$ normalizes to "entropy per matrix degree of freedom." The factor $1/N^2$ is the free probability analog of the $1/N$ in Shannon entropy for length-$N$ strings.

## Qubit Example ($d = 2$)

For a qubit density matrix $\rho$ with eigenvalues $p$ and $1-p$ (where $p > 1/2$), the explicit formula gives:

$$\chi(\rho) = 2\log|p - (1-p)| + \frac{2}{2}\log(2\pi e) + \frac{2 \cdot 1}{4}\log 2$$

$$= 2\log(2p - 1) + \log(2\pi e) + \frac{1}{2}\log 2$$

The eigenvalue-dependent part is $2\log(2p-1)$. For $p = 0.7$: this is $2\log(0.4) \approx -2.64$ (in nats) or $2\log_2(0.4) \approx -2.64$ bits. Notice that $\chi \to -\infty$ as $p \to 1/2$ (eigenvalues collide), reflecting the divergence that motivates the [[definitions/regularized-free-entropy|Regularized Free Entropy]] and the [[concepts/physical-free-entropy|Physical Free Entropy]].

## Used By

- [[concepts/free-entropy|Free Entropy]] (concept page)
- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[definitions/regularized-free-entropy|Regularized Free Entropy]]

## External References

- [Free entropy (Wikipedia)](https://en.wikipedia.org/wiki/Free_entropy)
- [Voiculescu, "Free entropy" (survey, 2002)](https://doi.org/10.1112/S0024609301008992)
