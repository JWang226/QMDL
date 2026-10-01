# Casimir Operator

**Appears in:** [[Article]], `lem:perturbation`, `eq:casimir_slice_gap`, `eq:casimir_deficit_compression`; earlier perturbation arguments appear in [[Notes]].

## Definition

For represented matrix units $E_{ij}$, the quadratic Casimir is

$$C_2=\sum_i H_i^2+
\sum_{\alpha>0}(E_{-\alpha}E_\alpha+E_\alpha E_{-\alpha}),\qquad H_i=E_{ii}.$$

On the irreducible representation of highest weight $\lambda$, it acts by

$$c_\lambda=(\lambda,\lambda+2\varrho),\qquad
\varrho_i=(d+1-2i)/2.$$

A Casimir eigenvalue need not distinguish every pair of irreducibles. The proof uses a specific positive gap between the Cartan constituent and lower constituents meeting a fixed weight sector.

## Localized Gap

Let $\nu=\mu+\omega$, with $\omega$ dominant but possibly signed. Embed $H_\nu$ in $H_\mu\otimes H_\omega$. At supported offset $\delta$, let $P_\delta$ project onto its weight-$\nu-\delta$ subspace and let

$$Q_\delta=\Pi_{\mu-\delta}\otimes|\omega\rangle\langle\omega|.$$

For $r\ge2$ and $|\delta|\le g_\mu$, shallow multiplicity equality gives equal ranks. On the **total-weight sector** $\mathcal W_{\nu-\delta}$, every other constituent has highest weight $\chi=\nu-\eta$ with both $\eta$ and $\delta-\eta$ in the positive root cone. Consequently,

$$c_\nu-c_\chi\ge(g_\mu+2)|\eta|\ge g_\mu+2.$$

If $S_\delta$ is the total-weight-sector projector and $K=c_\nu I-C_2$, the correctly localized inequality is

$$K\ge(g_\mu+2)(S_\delta-P_\delta).$$

It is not a claim with $I-P_\delta$ on the whole tensor product: other weights in the Cartan constituent also have Casimir eigenvalue $c_\nu$.

## Exact Compression and Trace Deficit

The root-exchange terms vanish after compression by $Q_\delta$, because its auxiliary factor is the highest-weight line. Thus

$$Q_\delta KQ_\delta=2(\delta,\omega)Q_\delta.$$

Compressing the localized gap yields

$$\operatorname{Tr}(Q_\delta-Q_\delta P_\delta Q_\delta)
\le\frac{2(\delta,\omega)}{g_\mu+2}\operatorname{Tr}Q_\delta.$$

Equal ranks and trace cyclicity give

$$\operatorname{Tr}(P_\delta-P_\delta Q_\delta P_\delta)
=\operatorname{Tr}(Q_\delta-Q_\delta P_\delta Q_\delta).$$

These are exactly the positive trace losses needed for the retained branches of the forward and reverse channels. Using $0\le(\delta,\omega)\le|\delta|\|\omega\|_1$ and averaging with the normalized weight coefficients gives the direct trace-distance bound. For $r=1$, only $\delta=0$ survives and the projectors agree.

## Relation to the Article and Lean

The Article also states the equal-rank operator-norm estimate

$$\|P_\delta-Q_\delta\|\le
\sqrt{2(\delta,\omega)/(g_\mu+2)}.$$

The formal channel proof takes the trace-deficit route above, which supplies the required channel error without assuming an operator-norm closeness lemma. `CasimirTrace`, `CartanTraceCloning`, `TensorSectorCasimir`, and `ConstructedLieCloning` contain the operator, representation, and channel steps. The underlying decomposition, root-cone constraints, and Casimir identities are constructed for the actual canonical modules. See [[proof-structure]].

The older $H_0+V$/Davis–Kahan account belongs to the Notes' proof development; it is not the dependency of the current Theorem 2 endpoint.

## Related

- [[results/lemmas/perturbation-lemma|Highest-Weight Subspace Perturbation]]
- [[definitions/edge-gap|Supported Row Gaps]]
- [[results/lemmas/tail-mass|Uniform Mean Depth]]
- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]]
