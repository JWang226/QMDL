# Probability Ratio (Lemma 9)

**Label:** `lem:ratio` (Article and Notes)
**Source:** Article line ~1664 (stated), ~2730 (proved); Notes line ~816

## Statement

Define the ratio:
$$Z(x) := \frac{x^\omega \cdot s_\mu(x)}{s_{\mu+\omega}(x)}$$

Then:
$$1 \geq Z(x) \geq 1 - O\left(e^{-(g_\mu + 1)\xi}\right)$$

where $\xi = \min_i(\ln x_i - \ln x_{i+1})$ is the logarithmic spectral gap.

## Intuition

The weight distributions of $\rho_\mu$ and $\rho_\nu$ (for $\nu = \mu + \omega$) are nearly identical. The ratio $p_\nu(\delta)/p_\mu(\delta) = Z(x)$ is independent of $\delta$ (a crucial simplification), and $Z(x)$ measures their overall agreement. When the spectral gap $\xi > 0$ and the edge gap $g_\mu$ is large (both guaranteed in the scaling regime), $Z(x)$ is exponentially close to 1 -- the "classical part" of the fidelity is essentially perfect.

The exponential suppression comes from a determinantal identity: both Schur polynomials are dominated by their identity-permutation term, and the non-identity permutations are exponentially suppressed by a factor related to the product of spectral gaps and row length differences.

## Proof Sketch

**Main idea:** (Upper bound) Kostka monotonicity gives a term-by-term inequality $x^\omega s_\mu(x) \leq s_{\mu+\omega}(x)$, so $Z \leq 1$. (Lower bound) Use the determinantal formula $s_\lambda(x) = \det(x_i^{\lambda_j+r-j})/\Delta(x)$. The identity permutation dominates each determinant (rearrangement inequality); non-identity terms are suppressed by $e^{-(g_\mu+1)\xi}$ because each adjacent transposition costs at least $(g_\mu+1)\xi$ in the exponent. The ratio of determinants is therefore $1 - O(e^{-(g_\mu+1)\xi})$.

---

### Extended Proof

### Upper Bound: $Z(x) \leq 1$ via Kostka Monotonicity

Expand the Schur polynomial into semistandard Young tableaux: $s_\mu(x) = \sum_{u \prec \mu} K_{\mu,u} \, x^u$. Multiplying by $x^\omega$ shifts weights: $x^\omega s_\mu(x) = \sum_u K_{\mu,u} \, x^{u+\omega}$.

By [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]], $K_{\mu, u} \leq K_{\mu+\omega, u+\omega}$ for every weight $u$. Since the weights of $\mu + \omega$ contain all shifted weights $u + \omega$ as a subset, every term in $x^\omega s_\mu(x)$ appears in $s_{\mu+\omega}(x)$ with a coefficient at least as large. Therefore $s_{\mu+\omega}(x) \geq x^\omega s_\mu(x)$, giving $Z(x) \leq 1$.

### Lower Bound: $Z(x) \geq 1 - O(e^{-(g_\mu+1)\xi})$ via Determinantal Formula

Since $x$ has exactly $r$ nonzero entries, the [[concepts/schur-polynomials|Schur Polynomials]] evaluate identically to those of $\mathrm{GL}(r)$. Using the determinantal formula $s_\lambda(x) = \det(x_i^{\lambda_j + r - j}) / \det(x_i^{r-j})$, the Vandermonde denominators cancel in $Z(x)$, leaving:

$$Z(x) = x^\omega \frac{\det(x_i^{\ell_j})}{\det(x_i^{L_j})}$$

where $\ell_j = \mu_j + r - j$ and $L_j = \ell_j + \omega_j$.

**Expand the determinants over $S_r$.** For the numerator:

$$\det(x_i^{\ell_j}) = \sum_{\sigma \in S_r} \mathrm{sgn}(\sigma) \prod_{j=1}^r x_j^{\ell_{\sigma(j)}} = \sum_{\sigma \in S_r} \mathrm{sgn}(\sigma) \, e^{\sum_j \ell_{\sigma(j)} \ln x_j}$$

Since both $\ell$ and $\ln x$ are strictly decreasing sequences, the identity permutation dominates: it achieves the maximum of $\sum_j \ell_{\sigma(j)} \ln x_j$ over all $\sigma$ (by the rearrangement inequality).

**Bound non-identity permutations.** For a single adjacent transposition $\tau = (k, k+1)$, the exponent changes by:

$$\Delta E = -(\ell_k - \ell_{k+1})(\ln x_k - \ln x_{k+1})$$

Now $\ell_k - \ell_{k+1} = \mu_k - \mu_{k+1} + 1 \geq g_\mu + 1$, and $\ln x_k - \ln x_{k+1} \geq \xi$. So:

$$|\Delta E| \geq (g_\mu + 1)\xi =: \epsilon_\mu$$

Every non-identity permutation can be reached by at least one adjacent transposition, so each non-identity term is suppressed by at least $e^{-\epsilon_\mu}$ relative to the identity term. There are $r! - 1$ such terms, giving:

$$\det(x_i^{\ell_j}) \geq x^\ell \left(1 - (r! - 1) e^{-\epsilon_\mu}\right)$$

**Similarly for the denominator** (with $L_j$ instead of $\ell_j$):

$$\det(x_i^{L_j}) \leq x^L \left(1 + (r! - 1) e^{-\epsilon_{\mu+\omega}}\right)$$

Since $\omega$ is dominant, $g_{\mu+\omega} \geq g_\mu$, so $\epsilon_{\mu+\omega} \geq \epsilon_\mu$.

**Combine.** The monomial prefactors give $x^\omega \cdot x^\ell / x^L = x^\omega \cdot x^\ell / x^{\ell + \omega} = 1$. Therefore:

$$Z(x) \geq \frac{1 - (r!-1)e^{-\epsilon_\mu}}{1 + (r!-1)e^{-\epsilon_\mu}} \geq 1 - 2(r!-1)e^{-\epsilon_\mu} = 1 - O(e^{-(g_\mu+1)\xi})$$

using the elementary inequality $(1-y)/(1+y) \geq 1 - 2y$.

## Dependencies

- [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] -- for the upper bound $Z(x) \leq 1$
- [[concepts/schur-polynomials|Schur Polynomials]] -- determinantal formula $s_\lambda(x) = \det(x_i^{\lambda_j+r-j})/\det(x_i^{r-j})$
- Rearrangement inequality (identity permutation dominates)

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- Step 5 (classical overlap bound)

## External References

- [Schur polynomial (Wikipedia)](https://en.wikipedia.org/wiki/Schur_polynomial)
- [Macdonald, *Symmetric Functions and Hall Polynomials* (Oxford University Press, 2nd ed., 1995)](https://global.oup.com/academic/product/symmetric-functions-and-hall-polynomials-9780198534891)
