# Schur Concentration and Atypical Mass

**Labels:** `lem:tail_prob`, `eq:tail_prob_bound` in the current [[Article]].
**Source:** [Article concentration lemma and tail estimate](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L788).
**Lean endpoint used by Theorem 1:** [FreeEntropy.SchurWeyl.physicalAtypicalMass_le_tailBound](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/SchurWeylConcentration.lean#L48).

## Statement

For a fixed spectrum $x_1>\cdots>x_r>0$, padded by zeros, the actual irreducible-sector probabilities of $\rho^{\otimes n}$ concentrate near the row $nx$. Define

$$
\epsilon_n=\sqrt{n/2}\log_2 n,\qquad
\mathcal T_{x,n}=\{\lambda\vdash n:\ell(\lambda)\le r,\quad
\max_{i\le r}|\lambda_i-nx_i|\le\epsilon_n\}.
$$

The **Article** gives the Schur-distribution event bound

$$
\Pr\!\left[d_{\mathrm{TV}}(\lambda/n,x)>t\right]
\le(n+1)^{r(r+1)/2}e^{-2nt^2},
\qquad t>0,
$$

and deduces

$$
\Pr[\lambda\notin\mathcal T_{x,n}]
\le(n+1)^{r(r+1)/2}
\exp\!\left(-\frac{(\log_2 n)^2}{4}\right).
$$

The **final physical Lean proof** establishes a sufficient bound with a coarser polynomial prefactor:

$$
\operatorname{physicalAtypicalMass}(x,n)
\le(n+1)^{K_d}
\exp\!\left(-\frac{(\log_2 n)^2}{4}\right),
\quad
K_d=(d-1)\binom d2+d,
\quad n\ge2.
$$

Consequently the actual atypical mass is eventually at most $1/n$. This is exactly [FreeEntropy.SchurWeyl.physicalAtypicalMass_eventually_le_inv](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/SchurWeylConcentration.lean#L62). The prefactor and the intermediate entropy inequality should not be conflated with the Article's sharper event bound.

## Intuition

Almost all the source lies in sectors whose highest row is close to $nx$. The squared logarithm in the exponential dominates every fixed polynomial prefactor. Therefore the weaker proved prefactor still makes the discarded tail negligible compared with $\log n/\sqrt n$.

## Proof Sketch

The physical proof begins with the actual constructed irreducible decomposition, not a supplied Schur probability formula.

1. Group sectors by their highest occupation $\lambda$. Orthogonal highest vectors with the same occupation inject into the corresponding word-type space, bounding their copy count.
2. The weight cone bounds each sector's diagonal monomials by the highest-weight monomial. A polynomial bound on sector dimension and the word-type count yield
   $$
   \Pr[\text{highest row }=\lambda]
   \le(n+1)^{(d-1)\binom d2}
   e^{-nD_{\mathrm{nat}}(\lambda/n\|x)}.
   $$
   Here $D_{\mathrm{nat}}$ uses natural logarithms. Unsupported rows have exactly zero mass.
3. The formal entropy estimate is the weaker Pinsker-type inequality
   $$
   D_{\mathrm{nat}}(p\|x)\ge\frac14\|p-x\|_1^2
   =d_{\mathrm{TV}}(p,x)^2.
   $$
   It follows through the squared Hellinger distance. The physical proof includes zero coordinates under the required support condition.
4. Equal total mass gives $|p_i-x_i|\le\frac12\|p-x\|_1$. Failure of the typical coordinate window therefore implies the sufficient lower bound
   $\|p-x\|_1\ge\log_2 n/\sqrt n$.
5. There are at most $(n+1)^d$ occupation rows. Sum the pointwise estimate and use the preceding separation to obtain the displayed physical tail bound.

The probabilities are constant along the unknown-unitary orbit. [FreeEntropy.SchurWeyl.physical_orbit_atypical_tail_le](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/SchurWeylConcentration.lean#L97) records the same estimate for every $U$.

## Lean Map

- [FreeEntropy.SchurWeyl.sectorsAt_card_le_words](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/SchurWeylConcentrationGrouping.lean#L65): actual copy-count bound.
- [FreeEntropy.SchurWeyl.highestSectorMass_le_exp_neg_kl](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/SchurWeylConcentrationProbability.lean#L55): actual pointwise physical probability bound.
- [FreeEntropy.FiniteConcentration.weak_pinsker](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/FiniteConcentration.lean#L108): the entropy inequality, with its precise constant.
- [FreeEntropy.SchurWeyl.physical_atypical_grouped_tail_le](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/SchurWeylConcentrationTail.lean#L169): typical-window tail.
- [FreeEntropy.Concentration.tailBound_eventually_le_inv](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/Concentration.lean#L62): fixed polynomial prefactors are asymptotically absorbed.

Earlier reusable lemmas accept a pointwise probability bound as a premise. The final physical endpoint above proves that input for the actual source; no concentration premise remains in Theorem 1.

## Dependencies

- [[concepts/schur-weyl-duality|Actual irreducible-sector decomposition]]
- Highest-weight classification, weight cones, and finite word-type counting
- Elementary relative-entropy and Hellinger estimates
- [[definitions/typical-set|Typical set]]

## Used By

- [[results/achievability|Theorem 1 achievability]]: bounds both atypical channel contributions
- [[results/converse|Theorem 1 converse]]: supplies the vanishing error of the physical-to-target comparison maps
