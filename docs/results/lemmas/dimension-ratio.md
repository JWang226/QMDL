# Dimension Ratio (Lemma 10)

**Label:** `lem:dim_ratio`
**Source:** Article line ~1776 (stated), ~2831 (proved)

## Statement

For $\nu = \mu + \omega$ in the scaling regime $g_\mu = \Theta(n)$, $\mu_r = \Theta(n)$, $|\omega| = o(n)$:

$$\frac{d_\mu}{d_\nu} = 1 - O\left(\frac{|\omega|}{n}\right) = 1 - O\left(\frac{d(\mu,\nu)}{n}\right)$$

## Intuition

When you add a small Young diagram $\omega$ to a large one $\mu$ to get $\nu = \mu + \omega$, the irrep dimensions $d_\mu$ and $d_\nu$ are nearly equal. The ratio deviates from 1 by at most $O(|\omega|/n)$.

## Proof Sketch

By the [[concepts/weyl-dimension-formula|Weyl dimension formula]], $d_\nu/d_\mu = \prod_{i < j} (1 + y_{ij})$ where $y_{ij} = (\omega_i - \omega_j)/(\mu_i - \mu_j + j - i)$. Split into three blocks:

1. **Nonzero vs. nonzero** ($1 \leq i < j \leq r$): denominators $\geq g_\mu = \Theta(n)$
2. **Nonzero vs. zero** ($1 \leq i \leq r < j \leq d$): denominators $\geq \mu_r = \Theta(n)$
3. **Zero vs. zero** ($r < i < j \leq d$): $y_{ij} = 0$

So $0 \leq y_{ij} \leq C|\omega|/n$ uniformly. With $O_d(1)$ factors, $\log(d_\nu/d_\mu) = O(|\omega|/n)$.

## Dependencies

- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]
- [[definitions/scaling-regime|Scaling Regime]]

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- ensures the normalization prefactor $\sqrt{d_\mu/d_\nu}$ in the block fidelity is close to 1, contributing only an $O(d(\mu,\nu)/n)$ correction
