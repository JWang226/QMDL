# Sanov's Theorem / Tail Probability (Lemma 12)

**Label:** `lem:tail_prob`
**Source:** Article line ~617; Notes line ~1136

## Statement

$$\Pr\left[\lambda : d(\lambda/n, p) > x\right] \leq (n+1)^{r(r+1)/2} e^{-2nx^2}$$

where $d(\lambda/n, p) = \frac{1}{2}\sum_i |\lambda_i/n - x_i|$ is the total variation distance between the empirical type $\lambda/n$ and the true spectrum $p$.

## Intuition

When you measure $\rho^{\otimes n}$ through the [[concepts/schur-weyl-duality|Schur Transform]], the resulting Young diagram $\lambda$ concentrates sharply near $np$. The probability of deviation $> x$ in total variation decays exponentially in $n$.

## Proof Sketch

This is a standard exponential concentration bound for the empirical type under i.i.d. sampling. The polynomial prefactor $(n+1)^{r(r+1)/2}$ is a union bound over the number of distinct types (partitions of $n$ with at most $d$ parts). The exponential $e^{-2nx^2}$ comes from Sanov's theorem: $q_{\lambda,n} \leq e^{-nD(\lambda/n \| p)}$ where $D$ is the KL divergence, combined with Pinsker's inequality $D(q\|p) \geq 2 d_{\mathrm{TV}}(q,p)^2$.

## Dependencies

- Sanov's theorem (large deviations)
- Pinsker's inequality

## Used By

- [[results/achievability|Achievability (State Compression)]] -- justifies restricting to the [[definitions/typical-set|Typical Set]] $\mathcal{T}_{p,n}$
- [[results/converse|Converse (State Compression)]] -- the atypical tail is exponentially small
