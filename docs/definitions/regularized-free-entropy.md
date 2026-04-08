# Regularized Free Entropy

**Label:** `eq:reg_free_ent` (Letter)
**Source:** Letter Eq. 10 (line ~161); Notes Eq. ~168

## Statement

For a $d \times d$ density matrix $\rho$ with distinct eigenvalues $p_1, \ldots, p_m$ having multiplicities $g_1, \ldots, g_m$:

$$\chi_{\mathrm{reg}}(\rho) = \frac{2}{d^2}\sum_{a < b} g_a g_b \log|p_a - p_b|$$

For the non-degenerate case ($g_i = 1$ for all $i$):

$$\chi_{\mathrm{reg}}(\rho) = \frac{2}{d^2}\sum_{i < j} \log|p_i - p_j|$$

## Intuition

The regularized free entropy is the "volume" part of the [[concepts/physical-free-entropy|Physical Free Entropy]] -- it captures how the eigenvalue spacings affect the size of the unitary orbit. Larger gaps between eigenvalues mean a "bigger" orbit (more room for the eigenbasis to vary), hence more bits needed to describe it.

Note: $\chi_{\mathrm{reg}}$ is always $\leq 0$ (since $|p_i - p_j| \leq 1$ for eigenvalues of density matrices), and $\chi_{\mathrm{reg}} \to -\infty$ as eigenvalues collide.

## Relation to Physical Free Entropy

$$\chi_{\mathrm{phy}}(\rho; \varepsilon) = d^2 \cdot \delta(\rho) \cdot \log(1/\varepsilon) + d^2 \cdot \chi_{\mathrm{reg}}(\rho) + \text{const} + O(\varepsilon)$$

## Role in QMDL

The regularized free entropy gives the **$O(1)$ correction** to the compression rate:

$$\log|M_n| = \underbrace{\frac{d^2 \delta(\rho)}{2}\log n}_{\text{leading}} + \underbrace{\sum_{i<j}\log|p_i - p_j|}_{\propto \chi_{\mathrm{reg}}} + \text{universal const} + o(1)$$

### Why $\chi_{\mathrm{reg}} \leq 0$ always

For a density matrix $\rho$ with eigenvalues $p_1, \ldots, p_d$ summing to 1, each eigenvalue satisfies $0 \leq p_i \leq 1$. Therefore every pairwise difference satisfies $|p_i - p_j| \leq 1$, which means $\log|p_i - p_j| \leq 0$ for all pairs. Since $\chi_{\mathrm{reg}}$ is a sum of such terms (with positive coefficients $2g_a g_b / d^2$), it is always non-positive:

$$\chi_{\mathrm{reg}}(\rho) = \frac{2}{d^2}\sum_{a < b} g_a g_b \log|p_a - p_b| \leq 0$$

Equality $\chi_{\mathrm{reg}} = 0$ would require every pair of distinct eigenvalues to differ by exactly 1, which for a probability distribution (with all $p_i \in [0,1]$) can only happen for a rank-1 projector (eigenvalues 1 and 0).

### What happens as eigenvalues collide

As two distinct eigenvalues $p_a$ and $p_b$ approach each other, $|p_a - p_b| \to 0$ and $\log|p_a - p_b| \to -\infty$. This drives $\chi_{\mathrm{reg}} \to -\infty$. Physically, this reflects the fact that when eigenvalues nearly coincide, the unitary orbit of $\rho$ shrinks (the eigenbasis becomes less distinguishable), so fewer bits are needed to describe it. In the QMDL formula, this means the $O(1)$ correction becomes very negative, reducing the required memory.

In the extreme limit of full degeneracy ($p_i = 1/d$ for all $i$), $\rho$ is the maximally mixed state with a trivial orbit (a single point), and no compression memory is needed at all.

## Qubit Example ($d = 2$)

For a qubit with eigenvalues $p$ and $1-p$ (non-degenerate, $p > 1/2$):

$$\chi_{\mathrm{reg}}(\rho) = \frac{2}{4}\log|p - (1-p)| = \frac{1}{2}\log(2p - 1)$$

| $p$ | $2p-1$ | $\chi_{\mathrm{reg}}$ (bits) |
|-----|--------|------|
| 0.9 | 0.8 | $-0.16$ |
| 0.7 | 0.4 | $-0.66$ |
| 0.6 | 0.2 | $-1.16$ |
| 0.51 | 0.02 | $-2.82$ |

As $p \to 1/2$, the gap closes and $\chi_{\mathrm{reg}} \to -\infty$. As $p \to 1$, the gap approaches 1 and $\chi_{\mathrm{reg}} \to 0$.

## Used By

- [[concepts/free-entropy|Free Entropy]]
- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[concepts/free-entropy-dimension|Free Entropy Dimension]]
- [[results/achievability|Achievability (State Compression)]]
- [[results/converse|Converse (State Compression)]]
