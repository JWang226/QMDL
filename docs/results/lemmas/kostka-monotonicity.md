# Multiplicity Monotonicity and Shallow Equality

**Labels:** `lem:kostka` and `lem:shallow_multiplicities` in the current Article.
**Source:** [monotonicity](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L1200) and [shallow multiplicities](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L1397).

These are two distinct assertions. “Adding a dominant weight” allows a signed integral difference; it need not mean adding boxes to every row.

## Statements

For dominant integral $\mu,\omega$ and any positive-root offset $\delta$,

$$m_\mu(\delta)\le m_{\mu+\omega}(\delta).$$

For $2\le r\le d$, put $g_\lambda=\min_{i<r}(\lambda_i-\lambda_{i+1})$. If $\delta\in Q_+^{(r)}$ and $|\delta|\le g_\lambda$, then

$$m_\lambda(\delta)=\mathsf P_r(\delta),$$

where $\mathsf P_r$ counts positive-root partitions of $\delta$ within the first $r$ coordinates. Since $g_{\mu+\omega}\ge g_\mu$, this gives

$$m_\mu(\delta)=m_{\mu+\omega}(\delta)\quad\text{when }|\delta|\le g_\mu.$$

At greater depths only the inequality is required. The multiplicity $m_\lambda(\delta)$ is a weight-space dimension, not the dimension of the whole irrep.

## Article proof and combinatorial formalization

The Article proves monotonicity by shifting a Gelfand–Tsetlin pattern columnwise:

$$m'_{i,j}=m_{i,j}+\omega_j.$$

One interlacing difference is unchanged; the other gains $\omega_j-\omega_{j+1}\ge0$. Row-sum differences show that the weight shifts by $\omega$, and subtracting $\omega_j$ recovers the original pattern. Thus the map is injective even for signed dominant $\omega$.

`FreeEntropy.GelfandTsetlin.multiplicity_mono` in [GelfandTsetlin.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/GelfandTsetlin.lean) proves this finite-pattern statement. [GTPartitions.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/GTPartitions.lean) also constructs vertical-drop root assignments and proves the shallow bijection, including `FreeEntropy.GelfandTsetlin.multiplicity_eq_kostantCount_of_shallow`.

## Actual representation-space route

The final cloning proof also connects these estimates to concrete matrix representations, rather than using a pattern count as an assumed representation dimension.

For monotonicity, the highest auxiliary slice of the Cartan projection intertwines raising operators and sends the source highest line nontrivially into the target. A nonzero kernel would be raising-invariant and would contain a highest vector, contradicting uniqueness of that line. The slice is therefore injective on each shifted weight space. This is `FreeEntropy.CartanLieCloning.cartanSlice_injective` and `FreeEntropy.CartanLieCloning.weight_multiplicity_add_le` in [CartanMultiplicity.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CartanMultiplicity.lean).

For shallow equality, ordered lowering monomials give the PBW upper bound. In the explicit exterior-power model, suitable lower-unitriangular minors give distinct monomials and hence independent coordinate functionals, yielding the matching lower bound. The results are assembled in [ExteriorMultiplicity.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/ExteriorMultiplicity.lean) and [ExteriorWeightMultiplicity.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/ExteriorWeightMultiplicity.lean), including `FreeEntropy.ExteriorRepresentation.canonicalWeight_card_eq_rootFiber`. Rank-support arguments restrict the count to the first $r$ coordinates.

This equality is needed for the shallow trace-deficit comparison; subspaces of different dimensions can still be compared, but that particular equal-rank argument would not apply. Deep weights use a separate trivial bound.

## Dependencies

- [[concepts/gelfand-tsetlin-basis|Gelfand–Tsetlin patterns]]
- [[concepts/kostant-partition-function|Positive-root partitions and depth]]
- Constructed Cartan embeddings, highest-weight uniqueness, and PBW spanning.

## Used By

- [[results/lemmas/perturbation-lemma|Local Casimir and projector deficits]]
- [[results/lemmas/probability-ratio|Eigenvalue ratio]]
- [[results/lemmas/tail-mass|Uniform mean depth]]
