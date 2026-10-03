# Highest-Weight Subspace Perturbation and Trace Deficits

**Label:** `lem:perturbation`; equations `eq:projector_casimir_bound`, `eq:casimir_slice_gap`, `eq:casimir_deficit_compression`.
**Source:** [current Article](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L1412).

## Statement

Use the supported rows and dominant difference $\omega=\nu-\mu$ of [[results/cloning-fidelity|Article Theorem 2]], and put $D=\|\omega\|_1$. Inside $\mathcal H_\mu\otimes\mathcal H_\omega$, define

$$P_\delta=V\Pi_{\nu-\delta}V^\dagger,\qquad
Q_\delta=\Pi_{\mu-\delta}\otimes|\omega\rangle\langle\omega|.$$

Both projectors lie in the total-weight sector $\nu-\delta$. For $r\ge2$, put $g_\mu=\min_{i<r}(\mu_i-\mu_{i+1})$. If $\delta\in Q_+^{(r)}$ and $|\delta|\le g_\mu$, their ranks agree and the Article proves

$$\|P_\delta-Q_\delta\|\le
\sqrt{\frac{2(\delta,\omega)}{g_\mu+2}}
\le\sqrt{\frac{2|\delta|D}{g_\mu+2}}.$$

For $r=1$, only the supported offset $\delta=0$ contributes and the projectors coincide. This is a finite statement, not an asymptotic assumption that $|\delta|^2\|\omega\|\ll n$.

## Local Casimir argument

On the total-weight sector, a constituent meeting the sector has highest row $\chi=\nu-\eta$, where both $\eta$ and $\delta-\eta$ belong to the positive-root cone. In particular, only supported simple roots occur. For any constituent other than the Cartan component,

$$c_\nu-c_\chi
=\sum_{i<r}\eta_i^{\mathrm{simple}}
\bigl[(\nu_i-\nu_{i+1})+(\chi_i-\chi_{i+1})+2\bigr]
\ge g_\mu+2.$$

Let $S_\delta$ denote the projector onto the whole total-weight sector and $A$ its compressed Casimir deficit. The useful inequality is local:

$$A\ge(g_\mu+2)(S_\delta-P_\delta).$$

It is not a gap assertion on the entire tensor-product space. Compressing onto $Q_\delta$ kills the root-exchange terms because the auxiliary factor is highest weight, leaving

$$Q_\delta A Q_\delta=2(\delta,\omega)Q_\delta.$$

These identities, with shallow rank equality, yield the displayed projector bound in the Article.

## Direct trace-deficit route in Lean

For the cloning estimate one can use traces directly. Define

$$T(P,Q)=\operatorname{Tr}[P(I-Q)P]\ge0.$$

The localized gap and compression identity imply, at shallow depths,

$$T(P_\delta,Q_\delta)\le e_\delta\operatorname{Tr}P_\delta,\qquad
T(Q_\delta,P_\delta)\le e_\delta\operatorname{Tr}Q_\delta,$$

where $e_\delta=\min\{1,2|\delta|D/(g_\mu+2)\}$. Equal ranks transfer one trace deficit to the other by cyclicity of trace. For integral $D\ge1$, deeper offsets satisfy $e_\delta=1$, and the trivial trace bound applies regardless of unequal ranks. Averaging these estimates preserves the linear $D/(b_\mu+1)$ error rate.

`FreeEntropy.CasimirTrace.traceDeficits_le_min_of_local_gap` in [CasimirTrace.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CasimirTrace.lean) is the matrix bridge. Actual Lie-generator identities and tensor decomposition discharge its gap and compression inputs in [LieMatrixCasimir.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/LieMatrixCasimir.lean), [CartanLieCloning.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CartanLieCloning.lean) and the canonical cloning construction. In particular, `FreeEntropy.CartanLieCloning.TensorDecomposition.local_gap` and `FreeEntropy.CartanLieCloning.tensor_weight_deficit` provide the local operator statements.

The final theorem certifies the resulting trace-distance bound. It does not rely on a standalone formalization of the historical Davis–Kahan/principal-angle fidelity argument.

## Dependencies

- [[concepts/casimir-operator|Quadratic Casimir]]
- [[results/lemmas/kostka-monotonicity|Shallow multiplicity equality]]
- [[results/propositions/choi-matrix-lemma|Cartan isometry]]

## Used By

- [[results/cloning-fidelity|Cloning accuracy]] — averaging positive projector losses.
