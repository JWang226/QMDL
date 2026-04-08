# Schur Polynomials

**Appears in:** [[Article]], [[Notes]]

## Intuition

Schur polynomials $s_\lambda(x_1, \ldots, x_d)$ are symmetric polynomials that serve as the characters of $\mathrm{GL}(d)$ representations. In this project, they play a dual role:
1. **Probability weights**: $s_\lambda(p)$ gives the probability of measuring sector $\lambda$ in the Schur transform
2. **Normalization**: $\rho_\lambda = \pi_\lambda(\rho)/s_\lambda(p)$ is the properly normalized GL irrep state

## Definition

$$s_\lambda(x) = \frac{\det[x_j^{\lambda_i + d - i}]_{i,j=1}^d}{\det[x_j^{d-i}]_{i,j=1}^d} = \frac{\det[x_j^{\lambda_i + d - i}]}{\prod_{i < j}(x_i - x_j)}$$

The denominator is the **Vandermonde determinant** $\Delta(x) = \prod_{i<j}(x_i - x_j)$.

## Key Properties Used in the Papers

1. **Weight decomposition**: $s_\lambda(x) = \sum_w K_{\lambda, w} \cdot x^w$ where $K_{\lambda,w}$ are [[results/kostka-monotonicity|Kostka numbers]]
2. **Trace formula**: $s_\lambda(x) = \mathrm{Tr}[\pi_\lambda(\mathrm{diag}(x))]$
3. **Ratio analysis**: The probability ratio $Z(x) = x^\omega s_\mu(x)/s_{\mu+\omega}(x)$ is central to [[results/probability-ratio|Probability Ratio (Lemma 9)]]

## Role in QMDL

The log Schur polynomial $\log s_\lambda(p)$ governs the probability of each Schur-Weyl sector. Via Sanov's theorem, sectors with $\lambda/n$ close to $p$ are exponentially more likely, concentrating the compression task on a small typical set.

## Related

- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- where Schur polynomials appear
- [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] -- weight multiplicities
- [[results/probability-ratio|Probability Ratio (Lemma 9)]] -- ratio of Schur polynomials

## External References

- [Schur polynomial (Wikipedia)](https://en.wikipedia.org/wiki/Schur_polynomial)
- [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd edition, Oxford University Press (1995)](https://doi.org/10.1017/S0013091500023592)
- R. P. Stanley, *Enumerative Combinatorics, Volume 2*, Cambridge University Press (1999)
- W. Fulton, *Young Tableaux*, Cambridge University Press (1997)
