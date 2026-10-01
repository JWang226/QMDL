# Cloning Accuracy (Article Theorem 2)

**Label:** `thm:main`; bound `eq:cloning_trace_bound`.
**Source:** [current Article, statement](https://github.com/JWang226/QMDL/blob/main/article.tex#L562) and [direct trace-distance proof](https://github.com/JWang226/QMDL/blob/main/article.tex#L1628).

This page retains its historical `cloning-fidelity` address. The current Article proves a finite **trace-distance** estimate. The historical Notes/fidelity argument and its numbering should not be substituted for this statement. The current Letter summarizes the compression construction but does not state a separately numbered cloning theorem. Article Theorem 1 is the optimal-memory result.

## Statement

Let $d\ge2$ and let $\rho$ have rank $1\le r\le d$ with nonzero eigenvalues $x_1>\cdots>x_r>0$, summing to one. Let $\mu,\nu\in\mathbb N^d$ be weakly decreasing rows, zero after coordinate $r$, and suppose $\omega=\nu-\mu$ is dominant. Define

$$
D=\sum_{i=1}^d|\nu_i-\mu_i|,\qquad
b_\mu=\min_{1\le i\le\min(r,d-1)}(\mu_i-\mu_{i+1}).
$$

For the normalized representation states $\rho_\mu,\rho_\nu$, both actual CPTP cloning maps satisfy

$$
\frac12\|\mathcal C_{\mu\to\nu}(\rho_\mu)-\rho_\nu\|_1
\le C_{d,x}\frac{D}{b_\mu+1},\qquad
\frac12\|\mathcal C_{\nu\to\mu}(\rho_\nu)-\rho_\mu\|_1
\le C_{d,x}\frac{D}{b_\mu+1}.
$$

These inequalities hold for every unitary eigenbasis, using the same channels. A proved explicit choice is

$$
q_x=\max_{i<r}\frac{x_{i+1}}{x_i},\quad N=\binom r2,\quad
K(x)=\frac{Nq_x}{(1-q_x)^{N+1}},\quad C_{d,x}=\binom d2+3K(x),
$$

with $q_x=K(x)=0$ for $r=1$. This is a sufficient common constant, not a claim of optimality.

The difference $\omega$ can have negative entries when $r=d$; the proof constructs the needed determinant-shifted auxiliary representation. When $r<d$, dominance and the zero tail force $\omega$ to be nonnegative. The bound includes zero row gaps, rank one, and $D=0$; in the last case the literal Cartan formulas are identity channels. For $r<d$, $b_\mu$ includes the gap $\mu_r$ to the zero row. No assumption such as $|\mu|=\Theta(n)$ is needed for the finite theorem. If $b_\mu=\Omega(n)$, it gives $O(D/n)$, and the compression application has $D=O(\sqrt n\log n)$.

## Intuition

The highest-weight branch of the cloner preserves most of each relevant weight block. A Casimir gap controls what this branch loses, while the geometric decay of the state's weight coefficients keeps the average loss bounded. Averaging those losses directly gives trace distance without a growing depth cutoff or a square-root conversion from fidelity.

## Proof route

1. **Construct representations and channels.** Exterior-power tensor models supply genuine irreducible highest-weight representations. Construct the Cartan isometry $V:\mathcal H_\nu\to\mathcal H_\mu\otimes\mathcal H_\omega$ and prove the forward and reverse maps are CPTP:
   $$\mathcal C_{\mu\to\nu}(X)=\frac{d_\mu}{d_\nu}V^\dagger(X\otimes I_\omega)V,\qquad
   \mathcal C_{\nu\to\mu}(Y)=\operatorname{Tr}_\omega(VYV^\dagger).$$
2. **Keep the auxiliary highest-weight branch.** Put $Jv=v\otimes|\omega\rangle$. In the total-weight sector $\nu-\delta$, compare the coupled projector $P_\delta$ with the product projector $Q_\delta=\Pi_{\mu-\delta}\otimes|\omega\rangle\langle\omega|$. Other Kraus branches contribute positive matrices.
3. **Bound local projector losses.** Shallow multiplicities agree. On the relevant weight sector the Casimir gap is at least $g_\mu+2$, where $g_\mu=\min_{i<r}(\mu_i-\mu_{i+1})$ for $r\ge2$. Compressing its deficit onto $Q_\delta$ gives $2(\delta,\omega)Q_\delta$. The formal proof can pass directly to trace deficits. For $D\ge1$, the bound is capped by
   $$e_\delta=\min\{1,\,2|\delta|D/(g_\mu+2)\}.$$
   At deeper weights the cap is one, so no equality of deep weight multiplicities is required.
4. **Average using a uniform first moment.** Root-partition counting and $p_\lambda(\delta)\le q_x^{|\delta|}$ prove $\sum_\delta |\delta|p_\lambda(\delta)m_\lambda(\delta)\le K(x)$ for both rows. Thus the averaged losses obey $M_\lambda\le2DK(x)/(g_\mu+2)$.
5. **Control scalar changes.** With $a=d_\mu/d_\nu$ and $Z=p_\nu(\delta)/p_\mu(\delta)$, Weyl dimensions give $1-a\le\binom d2D/(b_\mu+1)$; multiplicity monotonicity, shallow equality and the mean-depth bound give $1-Z\le K(x)/(g_\mu+1)$.
6. **Use positive remainders.** The retained forward branch lies above the target minus a positive remainder of trace at most $1-a+M_\nu$. The reverse output has a corresponding remainder of trace at most $1-Z+M_\mu$. These traces bound the full trace-distance errors. Since $b_\mu\le g_\mu$ and a nonzero integral $D$ is at least one, the common constant above follows. Rank one and coincident rows are handled separately.
7. **Identify the manuscript's maps.** Explicit reshuffling identifies these Cartan channels with the original normalized PRV Choi-projector contractions. The normalized adjoint is also proved to equal the literal Petz recovery expression. Covariance extends the estimates from diagonal states to all unitary eigenbases.

## Lean certificates

The following are final endpoints with only the stated spectrum, row, dominance and support hypotheses. Intermediate files with conditional interfaces are discharged in this construction.

| Form | Fully qualified declaration | File |
| --- | --- | --- |
| Constructed channels | `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy` | [Theorem2Canonical.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Theorem2Canonical.lean) |
| Literal Cartan formulas | `FreeEntropy.ExteriorRepresentation.theorem2_cartan_cloning_accuracy` | [Theorem2Canonical.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Theorem2Canonical.lean) |
| Original Choi contractions | `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi` | [Theorem2Choi.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Theorem2Choi.lean) |
| Literal Petz reverse | `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_petz` | [Theorem2Petz.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Theorem2Petz.lean) |

`FreeEntropy.Theorem2.cloningConstant` and `FreeEntropy.MeanDepth.meanDepthConstant` implement the displayed constants in [Theorem2.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Theorem2.lean) and [MeanDepth.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/MeanDepth.lean). The states are genuine normalized representation states; [CanonicalMonomialState.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalMonomialState.lean) connects their weight-coordinate description to physical tensor blocks.

## Dependencies

- [[results/propositions/choi-matrix-lemma|Cartan and Choi identification]]
- [[results/propositions/reverse-cloner|Reverse cloner and Petz recovery]]
- [[results/lemmas/kostka-monotonicity|Multiplicity monotonicity and shallow equality]]
- [[results/lemmas/perturbation-lemma|Local Casimir and projector deficits]]
- [[results/lemmas/tail-mass|Uniform mean depth]]
- [[results/lemmas/probability-ratio|Eigenvalue ratio]]
- [[results/lemmas/dimension-ratio|Weyl dimension ratio]]

## Used By

- [[results/achievability|Achievability]] — uniform approximation of typical sectors by one padded target.
- [[results/converse|Converse]] — transferring an arbitrary source code to the target orbit.
