# Converse (Theorem 1, lower bound)

**Labels:** `thm:qmdl`, `thm:converse` in the current [[Article]].
**Source:** [main statement](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L85), [converse proof](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L923).
**Lean endpoints:** [FreeEntropy.theorem1_converse](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/Theorem1Complete.lean#L43) and [FreeEntropy.theorem1_converse_of_uniform](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/Theorem1Complete.lean#L60).

The current [[Letter]] states the full-rank liminf converse immediately after `eq:result_qmdl` and refers to the companion Article for its proof. The Article supplies the rank-$r$ and Haar-average formulations stated here. The Letter's entropy equality describes an attaining sequence; arbitrary reliable codes satisfy a lower bound, not the same equality.

## Statement

Fix $1\le r\le d$ and $x_1>\cdots>x_r>0$ with $\sum_i x_i=1$, padded by zeros. Let $\rho_U=U\operatorname{diag}(x)U^\dagger$. Consider **any** sequence of CPTP encoders and decoders through memory $M_n$, independent of the unknown $U$.

If their normalized-Haar average error satisfies

$$
\overline\delta_n=
\int_{\mathrm U(d)}\frac12\left\|\mathcal D_n\mathcal E_n(\rho_U^{\otimes n})-\rho_U^{\otimes n}\right\|_1\,dU\longrightarrow0,
$$

then

$$
\liminf_{n\to\infty}\left[\log_2\dim M_n-L_{d,r}(n,x)\right]\ge0.
$$

Here $L_{d,r}$ is the full expression on the [[results/achievability|achievability page]], including its spectrum-dependent constant. The Lean statement uses an extended-real `liminf`, so it also covers sequences whose excess memory diverges. Equivalently, every fixed $\eta>0$ eventually satisfies $\log_2\dim M_n\ge L_{d,r}(n,x)-\eta$.

Vanishing worst-case error implies vanishing average error and therefore the same bound. No covariance, sectorwise behavior, or rate of error decay is assumed of the arbitrary code. The memory includes every retained classical register. The spectrum and dimension are fixed; rank one and $d=1$ are covered.

## Intuition

The [[results/achievability|achievability protocol]] provides accurate maps in both directions between the physical tensor source and one irreducible target orbit. Any smaller physical code would therefore compress that target orbit with vanishing error too. A quantitative orbit-memory inequality rules this out and retains the additive memory constant.

## Proof Sketch

### Transfer the arbitrary code to the padded target

Let $\mathcal A_n$ map the physical source into the padded target $\mathcal H_{\Lambda(n)}$, and let $\mathcal B_n$ map back. Their two comparison errors sum to a uniform bound $e_n=O(\log n/\sqrt n)$. For the target orbit state $\tau_{U,n}$, form

$$
\widetilde{\mathcal E}_n=\mathcal E_n\circ\mathcal B_n,
\qquad
\widetilde{\mathcal D}_n=\mathcal A_n\circ\mathcal D_n.
$$

These use the original memory $M_n$. Trace-distance contractivity and the triangle inequality imply

$$
\int T\bigl(\widetilde{\mathcal D}_n\widetilde{\mathcal E}_n(\tau_{U,n}),\tau_{U,n}\bigr)\,dU
\le\overline\delta_n+e_n.
$$

The literal physical-source statement is [FreeEntropy.SchurWeyl.actual_transferred_average_error_le](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/PhysicalCanonicalConverse.lean#L59).

### Use a uniform positive spectral gap

The [[results/propositions/orbit-sector-compression|compact-orbit memory bound]] gives

$$
\dim M_n\ge\dim\mathcal H_{\Lambda(n)}
\left(1-\frac{\overline\delta_n+e_n}{\gamma_*}\right),
$$

for a fixed positive lower bound $\gamma_*$ on the target state's top spectral gap. The checked final route uses

$$
q_x=\max_{1\le i<r}\frac{x_{i+1}}{x_i}<1,
\qquad
\gamma_*=(1-q_x)^{\binom d2+1}>0,
$$

with $q_x=0$ for $r=1$. The eigenvalue and counting estimates establishing this gap are proved for the actual canonical states. [FreeEntropy.SchurWeyl.physical_memory_bound_of_comparison](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/PhysicalCanonicalConverse.lean#L79) combines them with the transfer bound.

The Article's `lem:sector_gap` states the sharper bound $\gamma_x=(1-q_x)\prod_{i<j\le r}(1-x_j/x_i)$. The endpoint above uses the weaker $\gamma_*$; its positivity and independence of $n$ suffice for the exact asymptotic conclusion. This page does not identify the two constants.

### Take logarithms and the limit

Since $\overline\delta_n+e_n\to0$, the parenthesis tends to one and is eventually positive. Therefore

$$
\log_2\dim M_n\ge
\log_2\dim\mathcal H_{\Lambda(n)}
+\log_2\left(1-\frac{\overline\delta_n+e_n}{\gamma_*}\right)
=L_{d,r}(n,x)+o(1).
$$

The last step is the checked [[results/lemmas/weyl-dimension-asymptotic|padded-target dimension limit]]. The zero-cost $d=1$ case is handled separately before the final theorem combines all dimensions.

## Formalization Scope

The final theorem assumes only the fixed spectrum, actual CPTP codes, and convergence of their actual Haar-average error. It does not assume a decomposition, a gap, a transfer estimate, or a dimension formula. The worst-case corollary uses the proved inequality between average error and the actual supremum over $U$.

Earlier wiki versions described a good-sector/Markov argument followed by exact [[concepts/koashi-imoto|Koashi–Imoto]] incompressibility. That is not the current Article or Lean proof of the approximate converse. Exact incompressibility alone does not supply the quantitative estimate needed for this varying family of representations. The current proof transfers to the padded target and uses the finite spectral-gap bound directly.

## Dependencies

- [[results/achievability|Uniform forward and reverse physical comparison channels]]
- [[results/propositions/orbit-sector-compression|Quantitative compact-orbit memory bound]]
- Actual canonical irreducibility and the uniform positive top spectral gap
- [[results/lemmas/weyl-dimension-asymptotic|Padded-target memory expansion]]

## Used By

- [[concepts/quantum-minimum-description-length|Quantum minimum description length]]: optimality through the additive constant
