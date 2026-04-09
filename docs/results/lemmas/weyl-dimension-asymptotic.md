# Asymptotic Weyl Dimension (Lemma 11)

**Label:** `lem:weyl_asymptotic`
**Source:** Article line ~521

## Statement

For a partition $\lambda$ with $\lambda_i = nx_i + O(\sqrt{n}\Delta_n)$ for $1 \leq i \leq r$ and $\lambda_i = 0$ for $i > r$ (with $\Delta_n = o(\sqrt{n})$):

$$\log \dim \mathcal{H}_\lambda = \frac{r(2d-r-1)}{2}\log n + \sum_{i < j \leq r} \log(x_i - x_j) + (d-r)\sum_i \log x_i - \sum_{k=d-r}^{d-1} \log k! + O\left(\frac{\Delta_n}{\sqrt{n}}\right)$$

## Intuition

This is the key formula connecting irrep dimensions to the QMDL rate. It says $\log \dim \mathcal{H}_\lambda$ has a universal leading term $\frac{r(2d-r-1)}{2}\log n$ (depending only on dimension $d$ and rank $r$) plus a state-dependent correction involving the Vandermonde-like products $\prod(x_i - x_j)$ and $\prod x_i^{d-r}$.

## Proof Sketch

The exact [[concepts/weyl-dimension-formula|Weyl dimension formula]] is $\dim \mathcal{H}_\lambda = \prod_{1 \leq i < j \leq d} (\lambda_i - \lambda_j + j - i)/(j - i)$. Split the product into three blocks based on the rank $r$:

1. **Nonzero vs. nonzero** ($i < j \leq r$): $\lambda_i - \lambda_j = n(x_i - x_j)(1 + O(\Delta_n/\sqrt{n}))$, contributing $n^{r(r-1)/2} \prod_{i<j\leq r}(x_i - x_j)$.
2. **Nonzero vs. zero** ($i \leq r < j$): $\lambda_i + j - i = nx_i(1 + O(\Delta_n/\sqrt{n}))$, contributing $n^{r(d-r)} \prod_i x_i^{d-r}$.
3. **Zero vs. zero** ($r < i < j$): exactly $j - i$, giving $\prod_{k=1}^{d-r-1} k!$.

The total power of $n$ is $r(r-1)/2 + r(d-r) = r(2d-r-1)/2$. Taking logarithms, the $(1 + O(\Delta_n/\sqrt{n}))$ correction becomes additive $O(\Delta_n/\sqrt{n})$.

## Dependencies

- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]

## Used By

- [[results/achievability|Achievability (State Compression)]] -- computes $\log \dim \mathcal{H}_{\Lambda^*}$ for the optimal partition
- [[results/converse|Converse (State Compression)]] -- evaluates $\log \dim \mathcal{H}_{\lambda^{(n)}}$ for typical $\lambda^{(n)}$
