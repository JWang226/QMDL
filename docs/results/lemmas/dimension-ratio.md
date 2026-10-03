# Weyl Dimension-Ratio Bound

**Label:** `lem:dim_ratio` in the current [[Article]].
**Source:** [Article finite dimension-ratio lemma](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L1598).
**Lean theorem:** [FreeEntropy.ExteriorRepresentation.canonical_dimensionRatio_deficit](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CanonicalDimensionRatio.lean#L72).

## Statement

Let $d\ge2$, $1\le r\le d$, and let $\mu,\nu$ be dominant natural rows supported on the first $r$ coordinates. Assume the integral difference $\omega=\nu-\mu$ is dominant. Its entries may be negative. Set

$$
D=\sum_{i=1}^d|\omega_i|,
\qquad
b_\mu=\min_{1\le i\le\min(r,d-1)}(\mu_i-\mu_{i+1}),
\qquad
d_\lambda=\dim\mathcal H_\lambda.
$$

Then

$$
0\le1-\frac{d_\mu}{d_\nu}
\le\sum_{i<j}\frac{\omega_i-\omega_j}{\mu_i-\mu_j+j-i}
\le\binom d2\frac{D}{b_\mu+1}.
$$

This is a finite bound, with no asymptotic scaling assumption. The Lean endpoint proves the last bound for the actual canonical dimensions, and [FreeEntropy.ExteriorRepresentation.canonical_dimensionRatio_pos_le_one](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CanonicalDimensionRatio.lean#L54) proves $0<d_\mu/d_\nu\le1$.

The generic formal lemma is slightly more flexible: $b\ge0$ can be any lower bound on the relevant adjacent gaps, $D$ any upper bound on the row L1 difference, and the rows need only agree beyond the specified rank. Theorem 2 instantiates these parameters with the computed $b_\mu$ and exact $D$.

## Intuition

Dominance of the difference means every pairwise row gap can only increase, so the target dimension is at least the source dimension. The dimension loss is controlled by how much the row gaps change relative to their initial separation. A uniform shift of every row leaves the dimension unchanged, even when that shift is negative.

## Proof Sketch

The actual [[results/lemmas/weyl-dimension-asymptotic|Weyl dimension formula]] gives

$$
\frac{d_\mu}{d_\nu}
=\prod_{i<j}(1-a_{ij}),
\qquad
a_{ij}=\frac{\omega_i-\omega_j}{\nu_i-\nu_j+j-i}\in[0,1).
$$

Apply $1-\prod_k(1-a_k)\le\sum_k a_k$ and use the source denominators as smaller lower bounds. If $i>r$, the numerator is zero. Otherwise

$$
0\le\omega_i-\omega_j\le|\omega_i|+|\omega_j|\le D,
\qquad
\mu_i-\mu_j+j-i\ge b_\mu+1.
$$

There are at most $\binom d2$ pairs. This proves the bound, including $D=0$ and $b_\mu=0$.

For typical rows in Theorem 1, $D=O(\sqrt n\log n)$ and $b_\mu=\Omega(n)$, giving $1-d_\mu/d_\nu=O(\log n/\sqrt n)$. Older wiki statements presented only an asymptotic ratio; the current Article and checked channel proof use this explicit finite inequality.

## Dependencies

- [[results/lemmas/weyl-dimension-asymptotic|Exact dimensions of the canonical representations]]
- [[definitions/distance-between-irreps|Row L1 difference]]
- [[definitions/edge-gap|Supported adjacent-row gap]]
- Elementary product-deficit inequality

## Used By

- [[results/cloning-fidelity|Theorem 2 finite cloning bound]]: controls the dimension normalization loss
- [[results/achievability|Theorem 1 achievability]]: applies it uniformly to typical rows and their padded target
