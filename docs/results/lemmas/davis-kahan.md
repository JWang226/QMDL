# Davis–Kahan Perturbation Theory — Historical Background

**Status:** Background for an older fidelity proof route. The historical wiki used `lem:davis_kahan`; this label is absent from the current root `article.tex`. It is not a current Article lemma number or a separately certified theorem in this development.

## Idea

Spectral separation limits how far an eigenspace can move under a Hermitian perturbation. Davis–Kahan estimates make this principle quantitative, with hypotheses specifying the spectral clusters being compared. A gap in the unperturbed spectrum alone does not justify every proposed sharp denominator or cluster-identification rule.

A simple residual estimate illustrates the mechanism. Let $H$ be Hermitian, $v$ a unit vector, and $P$ a spectral projector of $H$. If every eigenvalue of $H$ on the orthogonal complement of $P$ is at distance at least $\eta>0$ from a real number $\lambda$, then

$$\|(I-P)v\|\le\frac{\|(H-\lambda I)v\|}{\eta}.$$

Expanding $v$ in an eigenbasis proves this by bounding each unwanted component. General subspace perturbation theorems extend this idea; the one-vector formula is not a complete statement of every Davis–Kahan variant.

## Current proof route

The present Article avoids the older perturbation expansion $H=H_0+V$ and its cutoff restrictions in the cloning argument. Instead, [[results/lemmas/perturbation-lemma|the current subspace lemma]] derives an exact compressed Casimir identity and a gap **within the relevant total-weight sector**. The formal proof then bounds trace deficits directly and averages them using [[results/lemmas/tail-mass|uniform mean depth]].

The resulting [[results/cloning-fidelity|Theorem 2]] has error $C_{d,x}D/(b_\mu+1)$ without a freely chosen $n^\varepsilon$ cutoff. [CartanLieCloning.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CartanLieCloning.lean) and [CasimirTrace.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CasimirTrace.lean) contain the checked local gap and trace-deficit route; this page records historical context rather than an additional dependency of that endpoint.

## Dependencies

- Finite-dimensional Hermitian spectral theory.

## Used By

- Historical explanation of eigenspace stability; see [[results/lemmas/perturbation-lemma|the current replacement argument]].

## External reference

- [Davis and Kahan, “The rotation of eigenvectors by a perturbation. III” (1970)](https://doi.org/10.1137/0707001).
