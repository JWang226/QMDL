# Principal Angles — Historical Proof Background

**Status:** Background for the older fidelity argument. The historical wiki referred to `lem:principle_angles`; that label is absent from the current root `article.tex`. It is not a current Article lemma number or a separate audited Lean endpoint.

## Linear-algebra identity

For orthogonal projectors $P,Q$, let $k=\min(\operatorname{rank}P,\operatorname{rank}Q)$ and let $\theta_1,\ldots,\theta_k$ be the principal angles between their ranges. Then

$$\operatorname{Tr}\sqrt{PQP}=\sum_{i=1}^k\cos\theta_i.$$

To see this, write $P=UU^\dagger$ and $Q=VV^\dagger$ with orthonormal-column matrices. The singular values of $U^\dagger V$ are $\cos\theta_i$, while $PQP$ has their squares as its possibly nonzero eigenvalues. Taking the positive square root and trace proves the identity. This concerns unnormalized projectors; normalizing them as states introduces rank factors.

## Relation to the current proof

The current [[results/lemmas/perturbation-lemma|subspace lemma]] still has geometric content: equal-rank projector distances can be interpreted through angles. But [[results/cloning-fidelity|Article Theorem 2]] is proved by a direct trace-distance argument. Its Lean route uses positive trace deficits

$$\operatorname{Tr}[P(I-Q)P]=\operatorname{Tr}P-\operatorname{Tr}(PQ),$$

a local Casimir gap, and a uniform mean-depth estimate. It does not pass through the sum of principal-angle cosines or claim the older $1-O(D/n^{1-\varepsilon})$ fidelity estimate as its main certificate.

See `FreeEntropy.CasimirTrace.traceDeficit_eq` and `FreeEntropy.CasimirTrace.traceDeficits_le_min_of_local_gap` in [CasimirTrace.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CasimirTrace.lean) for the checked quantities actually used.

## Dependencies

- Orthogonal projectors and singular values.

## Used By

- Historical fidelity-based interpretation of [[results/cloning-fidelity|cloning accuracy]].
- Geometric intuition for [[results/lemmas/perturbation-lemma|subspace comparison]].
