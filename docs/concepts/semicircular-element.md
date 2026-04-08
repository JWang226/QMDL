# Semicircular Element and Free Independence

**Appears in:** Letter, Notes (Sec. 2)

## Semicircular Element

A **semicircular element** $s$ in a tracial von Neumann algebra $(A, \tau)$ is a self-adjoint operator whose spectral measure is the **Wigner semicircle law**:

$$d\mu_s(t) = \frac{1}{2\pi}\sqrt{4 - t^2} \, dt, \quad t \in [-2, 2]$$

### Why "Semicircular"?

The name comes directly from the shape of the density function: $\frac{1}{2\pi}\sqrt{4 - t^2}$ is the equation of the upper half of a circle of radius 2 (scaled by $1/2\pi$). Plotting this density gives a semicircle sitting on the interval $[-2, 2]$. Compare this with the Gaussian density $\frac{1}{\sqrt{2\pi}}e^{-t^2/2}$, which has infinite tails -- the semicircular distribution has **compact support**, reflecting the boundedness of operators in a finite von Neumann algebra.

### The Semicircle Density Explicitly

The moments of the semicircular distribution are the **Catalan numbers**:

$$\tau(s^{2k}) = C_k = \frac{1}{k+1}\binom{2k}{k}, \qquad \tau(s^{2k+1}) = 0$$

The variance is $\tau(s^2) = 1$, and the fourth moment is $\tau(s^4) = 2$ (compared to 3 for the Gaussian -- the semicircular distribution has lighter tails).

This is the **free probability analogue of a Gaussian**: just as the Gaussian is the limit of sums of independent random variables (classical CLT), the semicircular law is the limit of sums of **freely independent** random variables (free CLT). In the random matrix realization, the empirical eigenvalue distribution of a Wigner matrix (symmetric with i.i.d. entries) converges to the semicircle law as $N \to \infty$.

## Free Independence (Freeness)

Two subalgebras $A_1, A_2 \subset A$ are **freely independent** if for all $a_i \in A_{j_i}$ with $\tau(a_i) = 0$ and alternating indices $j_1 \neq j_2 \neq \cdots$:

$$\tau(a_1 a_2 \cdots a_n) = 0$$

This replaces classical independence (factorization of joint moments) with a subtler "alternating vanishing" condition. The key model: if $U$ is a Haar-random unitary, then $A$ and $UAU^*$ are asymptotically freely independent.

## Role in the Project

1. **Free entropy dimension**: defined via perturbation by a freely independent semicircular: $\delta(a) = 1 + \lim_{\varepsilon \to 0} \chi(a + \varepsilon s)/(-\log\varepsilon)$
2. **Eigenvalue-eigenvector independence**: In the random matrix model for free entropy, eigenvalues and eigenvectors are "free" (independent in the free sense), which is why the volume of $\Omega_\varepsilon$ factorizes into a Vandermonde part (eigenvalues) and a unitary orbit part (eigenvectors)
3. **Free entropy conjecture**: The conjecture that free entropy = QMDL for all operators rests on the idea that quantum descriptions are governed by free (not classical) independence

## Related

- [[concepts/free-entropy|Free Entropy]]
- [[concepts/free-entropy-dimension|Free Entropy Dimension]]
- [[concepts/free-probability-theory|Free Probability Theory]]

## External References

- [Wigner semicircle distribution (Wikipedia)](https://en.wikipedia.org/wiki/Wigner_semicircle_distribution)
- [Free independence (Wikipedia)](https://en.wikipedia.org/wiki/Free_independence)
- D. Voiculescu, K. Dykema, and A. Nica, *Free Random Variables*, CRM Monograph Series, AMS (1992)
- A. Nica and R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University Press (2006)
