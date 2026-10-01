# Exact Weyl Dimension and the Memory Expansion

**Labels:** `eq:weyl_dim`, `lem:weyl_asymptotic` in the current [[Article]].
**Source:** [Article dimension lemma](https://github.com/JWang226/QMDL/blob/main/article.tex#L671).
**Lean endpoint for memory:** [FreeEntropy.ExteriorRepresentation.targetCanonicalDimension_log_asymptotic](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalDimension.lean#L86).

## Statement

For a dominant natural row $\lambda$ of length $d$, the actual canonical irreducible representation satisfies

$$
\dim\mathcal H_\lambda=
\prod_{1\le i<j\le d}\frac{\lambda_i-\lambda_j+j-i}{j-i}.
$$

Fix $x_1>\cdots>x_r>0$ and $x_i=0$ for $i>r$. The Article's quantitative asymptotic lemma assumes

$$
\lambda_i=nx_i+O(\sqrt n\,\zeta_n)\quad(i\le r),
\qquad
\lambda_i=0\quad(i>r),
\qquad
\zeta_n=o(\sqrt n),
$$

and concludes

$$
\log_2\dim\mathcal H_\lambda
=L_{d,r}(n,x)+O\!\left(\frac{\zeta_n}{\sqrt n}+\frac1n\right).
$$

The $1/n$ term accounts for the fixed shifts $j-i$ in the Weyl factors.

The checked endpoint needed for Theorem 1 proves the exact limit for the padded target of [[results/achievability|achievability]]:

$$
\log_2\dim\mathcal H_{\Lambda(n)}-L_{d,r}(n,x)\longrightarrow0.
$$

This is an assertion about the **actual constructed representation dimension**, with the Weyl formula proved first. The cited endpoint is the padded-target specialization; it does not claim every quantitative error variant of the Article's general lemma.

## Intuition

Each pair of unequal macroscopic row limits contributes one factor of $n$ to the dimension. Zero rows contribute no growth when paired with one another. The finite remaining product retains the eigenvalue gaps and factorial denominator, which become the additive constant after taking logarithms.

## Proof Sketch

### Split the Weyl product

The factors split into three classes:

- $i<j\le r$: numerator $n(x_i-x_j)\,[1+O(\zeta_n/\sqrt n+1/n)]$.
- $i\le r<j$: numerator $nx_i\,[1+O(\zeta_n/\sqrt n+1/n)]$.
- $r<i<j$: numerator exactly $j-i$, so the entire factor equals one.

There are

$$
\binom r2+r(d-r)=\frac{r(2d-r-1)}2
$$

active pairs. Their denominator is $\prod_{k=d-r}^{d-1}k!$. Hence

$$
\dim\mathcal H_\lambda=
\frac{n^{r(2d-r-1)/2}
\prod_{i<j\le r}(x_i-x_j)\prod_{i\le r}x_i^{d-r}}
{\prod_{k=d-r}^{d-1}k!}
\left[1+O\!\left(\frac{\zeta_n}{\sqrt n}+\frac1n\right)\right].
$$

Taking base-two logarithms gives the claimed expansion. For $\Lambda(n)$, the padding gives $\zeta_n=O(\log n)$.

### Prove the dimension formula for the constructed model

The Lean dependency chain also justifies the exact representation dimension, rather than inserting it as an axiom:

1. Exterior-power tensor spaces construct the canonical irreducible representation.
2. Its actual character satisfies the Casimir differential equation. Weight-cone support, permutation symmetry, and the unique highest line determine the Weyl alternant identity.
3. A finite polynomial coefficient extraction evaluates the character at the identity and produces a binomial determinant.
4. Interlacing-row recursion proves that determinant counts actual [[concepts/gelfand-tsetlin-basis|Gelfand–Tsetlin patterns]]. Its product formula is the Weyl product.
5. Finite-product asymptotics, the active-root count, and the factorial identity give the padded target's logarithmic limit.

## Lean Map

- [FreeEntropy.ExteriorRepresentation.canonicalCharacter_identity](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalCharacterIdentity.lean#L91): actual Weyl character identity.
- [FreeEntropy.WeylCharacter.dimension_eq_GT_of_character_identity](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/WeylDimensionExtraction.lean#L55): finite coefficient extraction.
- [FreeEntropy.GTDimension.card_eq_binomialDet](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/GTCardinality.lean#L75): combinatorial cardinality formula.
- [FreeEntropy.ExteriorRepresentation.canonical_dimension_fullWeyl](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalDimension.lean#L27): actual full Weyl dimension.
- [FreeEntropy.ExteriorRepresentation.canonical_dimension_activeWeyl](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalDimension.lean#L37): the zero-padded rank-supported product.
- [FreeEntropy.ExteriorRepresentation.targetCanonicalDimension_weyl](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalDimension.lean#L81) and the asymptotic endpoint above: actual memory dimension.

## Dependencies

- [[concepts/weyl-dimension-formula|Weyl dimension formula]]
- [[concepts/vandermonde-determinant|Alternants and Vandermonde determinants]]
- [[concepts/gelfand-tsetlin-basis|Interlacing patterns]]
- [[results/achievability|The padded target row]]

## Used By

- [[results/achievability|Theorem 1 upper bound]] and [[results/converse|lower bound]], both using the same padded target
- [[results/lemmas/dimension-ratio|Finite dimension-ratio estimate]] for Theorem 2
