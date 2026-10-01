# Uniform Mean Depth and Tail Control

**Label:** `lem:tail`; first-moment bound `eq:uniform_mean_depth`.
**Source:** [current Article](https://github.com/JWang226/QMDL/blob/main/article.tex#L1507).

The historical page name is retained. The current lemma supplies a uniform first moment; the main proof does not choose a growing depth cutoff.

## Statement

For the strictly decreasing nonzero spectrum $x_1>\cdots>x_r>0$, define

$$q_x=\max_{i<r}x_{i+1}/x_i<1,\qquad N=\binom r2,\qquad
K(x)=\frac{Nq_x}{(1-q_x)^{N+1}}.$$

Set $q_x=K(x)=0$ when $r=1$. For every partition $\lambda$ supported on the first $r$ rows,

$$\sum_{\delta\in Q_+^{(r)}}|\delta|\,p_\lambda(\delta)m_\lambda(\delta)\le K(x).$$

Here $\delta=\sum_{i<r}c_i\alpha_i$ has depth $|\delta|=\sum_i c_i$. The coefficient $p_\lambda(\delta)=x^{\lambda-\delta}/s_\lambda(x)$ is an eigenvalue, whereas the block probability is $p_\lambda(\delta)m_\lambda(\delta)$. These block probabilities sum to one.

For an integer $T\ge0$, the immediate tail bound is

$$\sum_{|\delta|>T}p_\lambda(\delta)m_\lambda(\delta)\le\frac{K(x)}{T+1}.$$

## Proof sketch

The highest-weight monomial gives $s_\lambda(x)\ge x^\lambda$. Each simple-root step costs at most $q_x$, hence $p_\lambda(\delta)\le q_x^{|\delta|}$. PBW spanning bounds weight multiplicity by positive-root partitions. At depth $t$, their total number is at most

$$\sum_{|\delta|=t}m_\lambda(\delta)\le\binom{t+N-1}{N-1}\quad(r\ge2).$$

One concrete counting proof injects weighted root assignments into $N$-tuples of total degree $t$: put the unused degree into a distinguished root of height one. The weighted-depth equation recovers that coordinate, so the map is injective. This justifies the coefficient bound without treating a numerical generating-function inequality as coefficientwise evidence.

Summing the first moment gives

$$\sum_{t\ge0}t\binom{t+N-1}{N-1}q_x^t
=\frac{Nq_x}{(1-q_x)^{N+1}}.$$

The displayed tail estimate follows from $|\delta|\ge T+1$ on the tail. Rank one has only the supported highest-weight line and zero depth.

## Lean route

- `FreeEntropy.KostantCounting.card_positiveRootAssignments_le` in [KostantCounting.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/KostantCounting.lean) proves the finite combinatorial bound.
- `FreeEntropy.ExteriorRepresentation.canonical_offsetMultiplicity_rank_depth_le` in [RankRootCounting.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/RankRootCounting.lean) applies it to actual representation multiplicities using only roots within the rank support.
- `FreeEntropy.MeanDepth.hasSum_first_moment` and `FreeEntropy.MeanDepth.weight_mean_le` in [MeanDepth.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/MeanDepth.lean) supply the analytic summation.
- `FreeEntropy.Cloning.tail_mass_le_mean_div` in [Cloning.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Cloning.lean) is the finite tail estimate.

An exponential tail bound belongs to the older fidelity/cutoff discussion. It is not needed, or asserted as a separate sharp endpoint, by this first-moment route.

## Dependencies

- [[results/lemmas/kostka-monotonicity|Weight multiplicities and root partitions]]
- [[concepts/kostant-partition-function|Positive roots and depth]]

## Used By

- [[results/lemmas/probability-ratio|Eigenvalue ratio]]
- [[results/cloning-fidelity|Cloning accuracy]] — average of capped projector deficits.
