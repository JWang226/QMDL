# Weyl Dimension Formula

**Appears in:** [[Article]] (Lemma 11, Sec. 4), [[Letter]]

## Statement

The dimension of the $\mathrm{GL}(d, \mathbb{C})$ irreducible representation $H_\lambda$ with highest weight $\lambda = (\lambda_1, \ldots, \lambda_d)$ is:

$$\dim H_\lambda = \prod_{1 \leq i < j \leq d} \frac{\lambda_i - \lambda_j + j - i}{j - i}$$

Equivalently, using the [[concepts/vandermonde-determinant|Vandermonde Determinant]]:

$$\dim H_\lambda = \frac{\Delta(\lambda + \rho_W)}{\Delta(\rho_W)}$$

where $\rho_W = (d-1, d-2, \ldots, 1, 0)$ is the Weyl vector.

## Intuition

The dimension counts the number of [[concepts/gelfand-tsetlin-basis|GT patterns]] with top row $\lambda$. For large $\lambda$, the count is dominated by eigenvalue spacings (via the Vandermonde), which is why [[concepts/free-entropy|Free Entropy]] appears. The numerator $\prod_{i<j}(\lambda_i - \lambda_j + j - i)$ measures how "spread out" the partition is -- more spread means more GT patterns fit, hence higher dimension.

## Asymptotic Expansion (Lemma 11)

For $\lambda \approx np$ (i.e., $\lambda_i/n \approx p_i$) with $r$ nonzero eigenvalues, the asymptotic Weyl dimension formula gives:

$$\log \dim H_\lambda = \frac{r(2d-r-1)}{2}\log n + \sum_{i<j \leq r}\log(p_i - p_j) + (d-r)\sum_{i=1}^r \log p_i - \sum_{k=d-r}^{d-1}\log k! + O\left(\frac{\Delta_n}{\sqrt{n}}\right)$$

where $\lambda_i = n x_i + O(\sqrt{n}\Delta_n)$ for $1 \leq i \leq r$ and $\lambda_i = 0$ for $i > r$, with $\Delta_n = o(\sqrt{n})$.

This formula directly gives the [[concepts/quantum-minimum-description-length|QMDL]] rate.

### Derivation: Three-Block Decomposition

The proof splits the Weyl dimension product $\prod_{i<j} (\lambda_i - \lambda_j + j - i)/(j - i)$ into three blocks based on which rows are nonzero versus zero.

**Block 1: Nonzero vs. Nonzero ($1 \leq i < j \leq r$).** Both $\lambda_i$ and $\lambda_j$ are of order $n$. Substituting $\lambda_k = nx_k + O(\sqrt{n}\Delta_n)$:

$$\lambda_i - \lambda_j + j - i = n(x_i - x_j)(1 + O(\Delta_n/\sqrt{n}))$$

The denominator $j - i$ is $O(1)$, so each factor contributes $\sim n(x_i - x_j)$. Taking the product over all $\binom{r}{2}$ such pairs:

$$\prod_{1 \leq i < j \leq r} \frac{\lambda_i - \lambda_j + j - i}{j - i} = n^{r(r-1)/2} \cdot \prod_{1 \leq i < j \leq r}(x_i - x_j) \cdot (1 + O(\Delta_n/\sqrt{n}))$$

This is where the **Vandermonde determinant** $\prod_{i<j}(x_i - x_j)$ appears -- the same quantity that controls [[concepts/free-entropy|Free Entropy]].

**Block 2: Nonzero vs. Zero ($1 \leq i \leq r < j \leq d$).** Here $\lambda_j = 0$, so $\lambda_i - \lambda_j + j - i = nx_i(1 + O(\Delta_n/\sqrt{n}))$, while the denominator is still $j - i = O(1)$. There are $r(d-r)$ such pairs, giving:

$$\prod_{\substack{1 \leq i \leq r \\ r < j \leq d}} \frac{\lambda_i + j - i}{j - i} = n^{r(d-r)} \cdot \left(\prod_{i=1}^r x_i\right)^{d-r} \cdot (1 + O(\Delta_n/\sqrt{n}))$$

This is the **rank-deficient contribution**: when $\rho$ has rank $r < d$, the zero eigenvalues create additional factors of $x_i$ from the nonzero eigenvalues coupling to the empty rows.

**Block 3: Zero vs. Zero ($r < i < j \leq d$).** Both rows are empty ($\lambda_i = \lambda_j = 0$), so $\lambda_i - \lambda_j + j - i = j - i$ exactly cancels the denominator. This block contributes a pure combinatorial constant:

$$\prod_{r < i < j \leq d} \frac{j - i}{j - i} = 1$$

Wait -- this contributes 1 to the numerator-over-denominator ratio. But we need to account for the denominator of the full formula. The denominator is $\prod_{1 \leq i < j \leq d}(j-i) = \prod_{k=1}^{d-1} k!$. The numerator's Block 3 contributes $\prod_{r < i < j \leq d}(j-i) = \prod_{k=1}^{d-r-1} k!$. So dividing:

$$\frac{\text{Block 3 of numerator}}{\text{full denominator}} \to \frac{\prod_{k=1}^{d-r-1} k!}{\prod_{k=1}^{d-1} k!} = \frac{1}{\prod_{k=d-r}^{d-1} k!}$$

**Combining all three blocks.** The total power of $n$ is:

$$n^{r(r-1)/2} \cdot n^{r(d-r)} = n^{r(r-1)/2 + r(d-r)} = n^{r(2d-r-1)/2}$$

Taking logarithms, the multiplicative error $(1 + O(\Delta_n/\sqrt{n}))$ becomes additive $O(\Delta_n/\sqrt{n})$, yielding the final formula.

### Reading the formula term by term

| Term | Origin | Interpretation |
|---|---|---|
| $\frac{r(2d-r-1)}{2}\log n$ | Blocks 1+2 powers of $n$ | Dimension of the [[concepts/flag-manifold|Flag Manifold]] $\times \frac{1}{2}$ |
| $\sum_{i<j \leq r}\log(x_i - x_j)$ | Block 1 Vandermonde | [[concepts/free-entropy|Free Entropy]] / eigenvalue repulsion |
| $(d-r)\sum_i \log x_i$ | Block 2 rank-deficiency | Coupling of nonzero eigenvalues to null space |
| $-\sum_{k=d-r}^{d-1}\log k!$ | Block 3 combinatorial | Universal constant independent of $\rho$ |

## Related

- [[concepts/vandermonde-determinant|Vandermonde Determinant]]
- [[concepts/free-entropy|Free Entropy]] -- appears as the subleading $O(1)$ term
- [[concepts/flag-manifold|Flag Manifold]] -- its dimension gives the leading $\log n$ coefficient
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- context where $\dim H_\lambda$ determines memory cost
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- the compression rate equals $\log \dim H_{\Lambda^*}$

## External References

- [Weyl character formula (Wikipedia)](https://en.wikipedia.org/wiki/Weyl_character_formula)
- [W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics, Springer (1991)](https://doi.org/10.1007/978-1-4612-0979-9)
- J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Graduate Texts in Mathematics, Springer (1972)
