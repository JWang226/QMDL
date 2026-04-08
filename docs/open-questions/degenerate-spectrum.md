# Open: QMDL for Degenerate Spectrum

**Source:** Letter Appendix B (line ~408); Article line ~131, ~797
**Status:** Open

## Context

All main theorems in the Article assume that $\rho$ has **strictly non-degenerate** positive eigenvalues $x_1 > x_2 > \cdots > x_r > 0$. This non-degeneracy is used in several critical places:

1. **Edge gap $g_\lambda = \Theta(n)$**: The [[definitions/edge-gap|edge gap]] of typical Young diagrams $\lambda \approx nx$ satisfies $g_\lambda \approx n \min_i(x_i - x_{i+1}) = \Theta(n)$ only when consecutive eigenvalues are distinct. This gap drives the spectral gap $\Delta = \Theta(n)$ in the [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]].

2. **Kostka monotonicity equality**: The equality $K_{\mu, \mu-\delta} = K_{\nu, \nu-\delta}$ in [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] holds when $|\delta| \leq g_\mu$. A vanishing edge gap breaks this.

3. **Probability ratio**: The exponential bound $Z(x) \geq 1 - O(e^{-(g_\mu+1)\xi})$ in [[results/probability-ratio|Probability Ratio (Lemma 9)]] depends on the logarithmic spectral gap $\xi = \min_i(\ln x_i - \ln x_{i+1}) > 0$.

4. **Converse (Lagrange interpolation)**: The proof that the orbit ensemble generates $\mathcal{B}(\mathcal{H}_\lambda)$ uses Lagrange interpolation to extract the highest-weight projector, which requires distinct eigenvalues of $\rho_\lambda$.

When eigenvalues collide ($x_i = x_{i+1}$ for some $i$), the unitary orbit of $\rho$ shrinks — rotations within degenerate eigenspaces are undetectable. The [[concepts/flag-manifold|flag manifold]] changes from $U(d)/U(1)^d$ to $U(d)/(U(g_1) \times \cdots \times U(g_k))$, reducing the number of degrees of freedom.

## The Expected Answer

The Letter (Appendix B) gives the free entropy formula for degenerate spectrum. For distinct eigenvalues $p_1 < \cdots < p_k$ with multiplicities $g_1, \ldots, g_k$ ($\sum_a g_a = d$):

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = \left(d^2 - \sum_a g_a^2\right) \log \varepsilon^{-1} + 2\sum_{a < b} g_a g_b \log|p_a - p_b| + \mathrm{const}$$

The [[concepts/free-entropy-dimension|free entropy dimension]] becomes $\delta(\rho) = 1 - \sum_a g_a^2/d^2$, and the expected QMDL rate is:

$$\log|M_n| = \frac{d^2 - \sum_a g_a^2}{2} \log n + O(1)$$

The Letter states: "We expect that with a more careful analysis for $\rho$ with a degenerate spectrum, the QMDL of any density operator $\rho^{\otimes n}$ can be shown to be the free entropy."

## What Needs to Be Done

### Achievability

The compression protocol should still work: the Schur transform decomposes $\rho^{\otimes n}$ into sectors, and the generalized cloning map can still be applied. The main technical issue is that typical Young diagrams $\lambda \approx nx$ now have **rows of equal length** (when $x_i = x_{i+1}$), so the edge gap $g_\lambda$ no longer grows with $n$ for those pairs. The Casimir perturbation argument breaks down at those specific row boundaries.

A possible approach: decompose the problem according to the block structure of the degenerate eigenspaces. Within each degenerate block, the state is effectively maximally mixed, so no eigenbasis information needs to be stored. The compression only needs to handle the inter-block structure, which lives on the smaller flag manifold $U(d)/(U(g_1) \times \cdots \times U(g_k))$.

### Converse

The Lagrange interpolation trick (extracting $|v_\lambda\rangle\langle v_\lambda|$ as a polynomial in $\rho_\lambda$) fails when eigenvalues coincide, since the polynomial has repeated roots. A modified argument is needed — possibly using higher-order projectors or the full block structure of the degenerate eigenspaces.

## Related

- [[concepts/free-entropy|Free Entropy]] -- the degenerate formula
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- $\delta(\rho) = 1 - \sum_a g_a^2/d^2$
- [[concepts/flag-manifold|Flag Manifold]] -- the reduced orbit space under degeneracy
- [[definitions/edge-gap|Edge Gap]] -- vanishes at degenerate pairs
- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- currently requires non-degeneracy
- [[results/converse|Converse (State Compression)]] -- Lagrange interpolation step fails

## External References

- [Voiculescu, "Free Entropy" (2002)](https://doi.org/10.1112/S0024609301008992)
- [Hiai and Petz, *The Semicircle Law, Free Random Variables and Entropy* (2000)](https://bookstore.ams.org/view?ProductCode=SURV/77)
- [Flag manifold (Wikipedia)](https://en.wikipedia.org/wiki/Generalized_flag_variety)
