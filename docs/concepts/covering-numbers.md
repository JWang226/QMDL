# Covering Numbers (Kolmogorov $\varepsilon$-Entropy)

**Appears in:** Letter (Eq. 8), Notes (Sec. 2.2)

## Definition

For a subset $\Omega$ of a metric space and $\varepsilon > 0$, the **$\varepsilon$-covering number** $N(\Omega, \varepsilon)$ is the minimum number of $\varepsilon$-balls needed to cover $\Omega$.

The **Kolmogorov $\varepsilon$-entropy** is $\log N(\Omega, \varepsilon)$.

## Role in the Project

The [[concepts/physical-free-entropy|Physical Free Entropy]] is defined as the covering number of the set of Hermitian matrices with prescribed spectrum:

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = \log N(\Omega_\varepsilon, \varepsilon)$$

where the metric is the Hilbert-Schmidt norm.

## Example: Covering a Ball

The simplest example is the $\varepsilon$-covering number of a $d$-dimensional Euclidean ball of radius $R$. Each covering ball has volume proportional to $\varepsilon^d$, while the large ball has volume proportional to $R^d$. By a volume comparison argument:

$$N(B_d(R), \varepsilon) \sim \left(\frac{R}{\varepsilon}\right)^d$$

so the Kolmogorov $\varepsilon$-entropy is $\log N \sim d \log(R/\varepsilon)$. The dimension $d$ plays the role of the [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- it controls the leading $\log(1/\varepsilon)$ coefficient. The radius $R$ contributes a state-dependent constant. This is exactly the structure of the [[concepts/physical-free-entropy|Physical Free Entropy]]: $\chi_{\mathrm{phy}}(\rho; \varepsilon) = d^2 \delta(\rho) \log(1/\varepsilon) + \chi_{\mathrm{reg}}(\rho) + O(\varepsilon)$.

## Connection to Classical Information Theory (Kolmogorov-Tikhomirov)

Kolmogorov and Tikhomirov (1961) introduced $\varepsilon$-entropy as a measure of the "complexity" or "massiveness" of a compact set in a metric space. Their key insight was that $\log N(\Omega, \varepsilon)$ quantifies how many bits are needed to specify a point in $\Omega$ up to accuracy $\varepsilon$. This is a metric-geometric version of Shannon entropy: rather than counting typical sequences, one counts distinguishable points.

The physical free entropy extends this framework to the **non-commutative setting**: the set $\Omega_\varepsilon$ lives in the space of Hermitian matrices, and the metric is the Hilbert-Schmidt norm. The covering number then counts the number of "distinguishable quantum microstates" -- density matrices that are $\varepsilon$-separated in operator norm.

## References

- KolmogorovTikhomirov1961: Original $\varepsilon$-entropy paper
- Kolmogorov1963: Theory of transmission of information

## Related

- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[definitions/physical-free-entropy-def|Physical Free Entropy (Formal Definition)]]
