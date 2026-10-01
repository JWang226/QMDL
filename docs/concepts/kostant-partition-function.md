# Kostant Partition Function

**Appears in:** [[Article|current Article]], `sec:prelim`, `eq:verma_multiplicity_bound`, and `lem:tail`; also [[Notes|the earlier Notes]].

## Definition

The **Kostant partition function** $\mathfrak{K}(\delta)$ counts the number of ways to write $\delta \in Q_+$ (the monoid of nonnegative combinations of simple roots) as a sum of positive roots:

$$\mathfrak{K}(\delta) = \#\{(n_\alpha)_{\alpha \in \Phi^+} : \sum_\alpha n_\alpha \alpha = \delta, n_\alpha \in \mathbb{Z}_{\geq 0}\}$$

## Relation to Kostka Numbers

By Kostant's weight multiplicity formula:

$$K_{\lambda,\beta}=\sum_{u\in W}(-1)^{\ell(u)}\mathfrak K(u(\lambda+\rho_W)-(\beta+\rho_W))$$

where $W$ is the Weyl group and $\rho_W$ is the Weyl vector. The multiplicity upper bound used here is

$$K_{\lambda,\lambda-\delta}\le\mathfrak K(\delta).$$

Its direct justification is PBW spanning by ordered lowering monomials: the spanning words are indexed by root partitions. This inequality is not obtained merely by dropping terms from the alternating sum above. The full Kostant formula is background; the main Lean proof constructs the PBW bound directly.

## Example: $A_2$ (i.e., $\mathrm{GL}(3)$)

For $\mathrm{GL}(3)$, the positive roots are $\Phi^+ = \{\alpha_1, \alpha_2, \alpha_1 + \alpha_2\}$, where $\alpha_1 = e_1 - e_2$ and $\alpha_2 = e_2 - e_3$ are the simple roots.

**Compute $\mathfrak{K}(\alpha_1 + \alpha_2)$:** We need the number of ways to write $\delta = \alpha_1 + \alpha_2$ as a non-negative integer combination of positive roots:

$$n_1 \alpha_1 + n_2 \alpha_2 + n_3(\alpha_1 + \alpha_2) = \alpha_1 + \alpha_2$$

This gives $(n_1 + n_3)\alpha_1 + (n_2 + n_3)\alpha_2 = \alpha_1 + \alpha_2$, so $n_1 + n_3 = 1$ and $n_2 + n_3 = 1$. The solutions are:

| $n_1$ | $n_2$ | $n_3$ | Decomposition |
|---|---|---|---|
| 1 | 1 | 0 | $\alpha_1 + \alpha_2$ |
| 0 | 0 | 1 | $(\alpha_1 + \alpha_2)$ |

So $\mathfrak{K}(\alpha_1 + \alpha_2) = 2$. This means the weight space at offset $\alpha_1+\alpha_2$, of depth two, has dimension two in a Verma module. A finite-dimensional irreducible module can have smaller multiplicity unless the shallow-gap condition holds.

## Generating Function

The generating function for the Kostant partition function organized by height $t = |\delta|$ is:

$$\sum_{t \geq 0} A_r(t) \, q^t = \prod_{\alpha \in \Phi^+} \frac{1}{1 - q^{|\alpha|}}$$

where $A_r(t) = \sum_{|\delta| = t} \mathfrak{K}(\delta)$. For type $A_{r-1}$, there are exactly $r - h$ positive roots of height $h$, so:

$$\sum_{t \geq 0} A_r(t) \, q^t = \prod_{h=1}^{r-1} \frac{1}{(1-q^h)^{r-h}}$$

For $r\ge2$, counting assignments gives the finite bound $A_r(t)\le\binom{t+N-1}{N-1}$ with $N=\binom r2$, and hence a polynomial bound in $t$. Root height counts simple-root steps; it is not the number of positive-root factors in a partition.

## Role in the Current Proof

The actual PBW lowering span bounds each weight multiplicity by the number of positive-root assignments. For supported offsets, roots outside the first $r$ coordinates cannot contribute. Writing $N=\binom r2$, the proved depth envelope for $r\ge2$ is

$$\sum_{|\delta|=t}m_\mu(\delta)\le\binom{t+N-1}{N-1}.$$

This envelope and spectral decay $q_x^t$ give the uniform mean-depth estimate used in Article Theorem 2. At rank one only depth zero occurs and the mean depth is zero, so formulas involving $N-1$ are not applied at $N=0$.

`FreeEntropy.KostantCounting.card_positiveRootAssignments_le` in [KostantCounting.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/KostantCounting.lean) proves the finite counting bound. `FreeEntropy.ExteriorRepresentation.canonical_offsetMultiplicity_rank_depth_le` in [RankRootCounting.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/RankRootCounting.lean) proves the supported canonical envelope, and `FreeEntropy.MeanDepth.hasSum_first_moment` in [MeanDepth.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/MeanDepth.lean) proves the generating-series estimate. The coefficient bound is discharged for the actual states used in the final theorem. Older Notes discussions organized the estimate as a cutoff tail; the current proof averages the finite first moment directly. See [[proof-structure|the current proof map]].

## Related

- [[results/lemmas/tail-mass|Uniform Mean Depth]]
- [[definitions/kostka-number|Kostka Number]]
- [[results/lemmas/kostka-monotonicity|Multiplicity Monotonicity]]

## External References

- [Kostant partition function (Wikipedia)](https://en.wikipedia.org/wiki/Kostant_partition_function)
- J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Graduate Texts in Mathematics, Springer (1972)
- B. Kostant, "A formula for the multiplicity of a weight," *Trans. Amer. Math. Soc.* 93, 53--73 (1959)
