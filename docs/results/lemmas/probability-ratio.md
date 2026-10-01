# Eigenvalue Ratio

**Label:** `lem:ratio`.
**Source:** [current Article](https://github.com/JWang226/QMDL/blob/main/article.tex#L1551).

## Statement

Let $\mu,\nu$ be partitions supported on the first $r$ rows, with dominant $\omega=\nu-\mu$. For the fixed positive spectrum, put

$$Z(x)=\frac{x^\omega s_\mu(x)}{s_\nu(x)},\qquad
p_\nu(\delta)=Z(x)p_\mu(\delta).$$

The ratio is independent of the weight offset. For $r\ge2$, with $g_\mu=\min_{i<r}(\mu_i-\mu_{i+1})$ and the [[results/lemmas/tail-mass|uniform mean-depth constant]] $K(x)$,

$$0<Z(x)\le1,\qquad 0\le1-Z(x)\le\frac{K(x)}{g_\mu+1}.$$

For $r=1$, $Z(x)=1$.

## Intuition

The target may have more states at a given weight offset. Its normalizer must account for these additional multiplicities, so its individual eigenvalue is no larger. Shallow multiplicities agree, which confines any normalization difference to the deep tail.

The equation above compares **individual eigenvalue coefficients**. The block probabilities also contain multiplicities, so their ratio is generally not just $Z(x)$.

## Proof sketch

Normalization gives

$$1-Z(x)=\sum_\delta p_\nu(\delta)\bigl(m_\nu(\delta)-m_\mu(\delta)\bigr).$$

[[results/lemmas/kostka-monotonicity|Multiplicity monotonicity]] makes every summand nonnegative. Shallow equality makes the summands vanish for $|\delta|\le g_\mu$. Therefore

$$
1-Z(x)\le\sum_{|\delta|>g_\mu}p_\nu(\delta)m_\nu(\delta)
\le\frac{1}{g_\mu+1}\sum_\delta|\delta|p_\nu(\delta)m_\nu(\delta)
\le\frac{K(x)}{g_\mu+1}.
$$

This is a finite normalization-and-tail argument. The earlier determinant-dominance estimate $1-Z=O(e^{-c g_\mu})$ is not the estimate used by the current Article or the main Lean endpoint.

## Lean route

`FreeEntropy.Cloning.eigenvalue_ratio_deficit` in [Cloning.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Cloning.lean) proves the finite reduction. The actual normalizers, multiplicities and shallow equality are supplied in the canonical construction, culminating in `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy` in [Theorem2Canonical.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Theorem2Canonical.lean). The endpoint does not assume this ratio bound.

## Dependencies

- [[results/lemmas/kostka-monotonicity|Multiplicity monotonicity and shallow equality]]
- [[results/lemmas/tail-mass|Uniform mean depth and tail control]]

## Used By

- [[results/cloning-fidelity|Cloning accuracy]] — the reverse loss $1-Z(x)$ and forward comparison $p_\mu\ge p_\nu$.
