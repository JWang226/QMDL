# Reverse Cloner and Petz Recovery (Article Proposition 2)

**Label:** `prop:reverse`.
**Source:** [current Article](https://github.com/JWang226/QMDL/blob/main/article.tex#L540).

## Statement

For the generalized cloner $\mathcal C=\mathcal C_{\mu\to\nu}$ and the maximally mixed reference state $\sigma_\mu=I_\mu/d_\mu$, the Article states

$$\mathcal R_{\sigma_\mu,\mathcal C}=\mathcal C_{\nu\to\mu}
=\frac{d_\nu}{d_\mu}\mathcal C^\dagger.$$

The adjoint is the Hilbert–Schmidt adjoint. In the Cartan situation of [[results/cloning-fidelity|Theorem 2]], its explicit formula is

$$\mathcal C^\dagger(Y)=\frac{d_\mu}{d_\nu}\operatorname{Tr}_\omega(VYV^\dagger),\qquad
\mathcal C_{\nu\to\mu}(Y)=\operatorname{Tr}_\omega(VYV^\dagger).$$

This identity defines a canonical recovery channel. It does not claim that the channel exactly recovers every input state, or optimizes every possible recovery objective.

## Proof route

First prove the matrix trace-pairing identity that characterizes $\mathcal C^\dagger$. The forward Cartan map sends the maximally mixed source to the maximally mixed target:

$$\mathcal C(I_\mu/d_\mu)=I_\nu/d_\nu.$$

The actual Petz expression therefore simplifies as follows:

$$
\begin{aligned}
\mathcal R_{\sigma_\mu,\mathcal C}(Y)
&=\sigma_\mu^{1/2}\mathcal C^\dagger\!\left(
\mathcal C(\sigma_\mu)^{-1/2}Y\mathcal C(\sigma_\mu)^{-1/2}\right)\sigma_\mu^{1/2}\\
&=\frac{d_\nu}{d_\mu}\mathcal C^\dagger(Y)
=\operatorname{Tr}_\omega(VYV^\dagger).
\end{aligned}
$$

These reference states are faithful, so ordinary matrix inverses suffice even when the representation state being approximated comes from a rank-deficient $\rho$.

To identify the reverse map with the manuscript's reverse PRV formula, conjugate the forward Choi projector entrywise and exchange its two tensor factors. Its range carries the dual auxiliary representation with highest weight

$$\omega^*=(-\omega_d,\ldots,-\omega_1)=(\mu-\nu)^+.$$

The reverse Choi operator is $(d_\nu/d_\omega)\Pi_{\omega^*}$. The construction proves its highest-weight label, cyclic range and multiplicity one, so this is a specific original cloning map, not merely an unspecified CPTP recovery.

## Lean certificates and scope

For the canonical dominant-difference pairs of Theorem 2, all identities above hold on arbitrary matrices, including coincident rows.

| Fact | Declaration | File |
| --- | --- | --- |
| Genuine adjoint | `FreeEntropy.ExteriorRepresentation.canonicalAdjoint_hilbertSchmidt` | [CanonicalPetz.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalPetz.lean) |
| Normalized adjoint | `FreeEntropy.ExteriorRepresentation.canonicalReverse_eq_normalized_adjoint` | [CanonicalPetz.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalPetz.lean) |
| Literal Petz equality | `FreeEntropy.ExteriorRepresentation.canonicalPetz_eq_reverse` | [CanonicalPetz.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalPetz.lean) |
| Reverse Choi matrix | `FreeEntropy.ExteriorRepresentation.canonicalReverse_choi` | [CanonicalReverseChoi.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalReverseChoi.lean) |
| Dual highest-weight range | `FreeEntropy.ExteriorRepresentation.canonicalReverseChoi_highest_cyclic` | [ReverseChoiRepresentation.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/ReverseChoiRepresentation.lean) |
| Unique reverse component | `FreeEntropy.ExteriorRepresentation.canonicalReverseChoi_multiplicity_one` | [ReverseChoiMultiplicity.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/ReverseChoiMultiplicity.lean) |

The final `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_petz` in [Theorem2Petz.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Theorem2Petz.lean) gives the same finite error bound with the reverse map written as `FreeEntropy.Petz.recovery`, using matrix square roots and inverses. The broader Article proposition is stated for general PRV pairs; the audited endpoint covers the constructed Cartan pairs needed for the two main theorems.

## Dependencies

- [[results/propositions/choi-matrix-lemma|Cartan and Choi identification]]
- [[concepts/petz-recovery-map|Petz recovery map]]
- [[concepts/prv-component|Dual PRV component]]

## Used By

- [[results/cloning-fidelity|Cloning accuracy]] — reverse-direction retained-branch bound.
- [[results/achievability|Achievability]] — recovery from the common padded target.
