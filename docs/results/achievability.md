# Achievability (Theorem 1, upper bound)

**Labels:** `thm:qmdl`, `thm:achievability`, `eq:result` in the current [[Article]].
**Source:** [main statement](https://github.com/JWang226/QMDL/blob/main/article.tex#L85), [achievability section](https://github.com/JWang226/QMDL/blob/main/article.tex#L607).
**Lean endpoint:** [FreeEntropy.theorem1_achievability](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/Theorem1Complete.lean#L23).

## Statement

Fix $d\ge1$ and a known normalized spectrum $x_1>\cdots>x_r>0$, with $1\le r\le d$ and $x_i=0$ for $i>r$. The unknown state ranges over $\rho_U=U\operatorname{diag}(x)U^\dagger$, $U\in\mathrm U(d)$. There are CPTP encoders and decoders, depending on $n$ and $x$ but not on $U$, with

$$
\log_2\dim M_n=L_{d,r}(n,x)+o(1),
\qquad
\sup_U\frac12\left\|\mathcal D_n\mathcal E_n(\rho_U^{\otimes n})-\rho_U^{\otimes n}\right\|_1
=O\!\left(\frac{\log_2 n}{\sqrt n}\right)\longrightarrow0,
$$

where

$$
\begin{aligned}
L_{d,r}(n,x)={}&\frac{r(2d-r-1)}2\log_2 n
+\sum_{1\le i<j\le r}\log_2(x_i-x_j)\\
&+(d-r)\sum_{i=1}^r\log_2 x_i
-\sum_{k=d-r}^{d-1}\log_2(k!).
\end{aligned}
$$

The memory cost is the **logarithm of its dimension**, including any retained classical register. In the Article this cost is denoted $|M_n|$; in Lean, `memory n` is the dimension itself. Rounding to an integer number of qubits need not preserve the stated $o(1)$ remainder. This task reconstructs the state without requiring preservation of a purification.

The dimension, rank, and spectrum remain fixed in the limit. The bound is not uniform when positive eigenvalues collide or approach zero, and does not promise the same memory expansion for every prescribed error schedule. Rank one and $d=1$ are included; for $d=1$, a one-dimensional memory gives zero cost and zero error.

## Intuition

The spectrum is already known. The memory only needs to preserve information about the unknown eigenbasis. The representation carrying that information has polynomial dimension, hence logarithmic memory cost. The coefficient of $\log n$ is half the real dimension of the unitary orbit; the remaining terms retain the exact spectrum-dependent constant.

## Proof Sketch

### One padded memory space

Set

$$
\epsilon_n=\sqrt{n/2}\log_2 n,\qquad
\mathcal T_{x,n}=\left\{\lambda\vdash n:\ell(\lambda)\le r,
\ \max_{i\le r}|\lambda_i-nx_i|\le\epsilon_n\right\}.
$$

The target row is

$$
\Lambda_i=\begin{cases}
\left\lceil nx_i+(r-i+1)(2\epsilon_n+1)\right\rceil,&1\le i\le r,\\
0,&i>r.
\end{cases}
$$

For every typical $\lambda$, $\Lambda-\lambda$ is dominant and nonnegative. Its row distance is $D=O(\sqrt n\log n)$, while the supported adjacent gap of $\lambda$ is $\Omega(n)$. The crossing gap $\lambda_r-\lambda_{r+1}=\lambda_r$ is included when $r<d$. These facts are proved uniformly over typical rows in [FreeEntropy.TypicalRows.target_difference_dominant](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/TypicalRows.lean#L117) and [FreeEntropy.TypicalRows.cloning_envelope_le](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/TypicalRows.lean#L197).

### Physical channels

The actual tensor source is decomposed into irreducible sectors. The construction identifies each sector with its canonical highest-weight representation and proves the source block formula. Equivalent copies carry identical states; in the usual grouped Schur notation the multiplicity register is maximally mixed.

The encoder measures the sector, discards multiplicity information, and applies the forward [[results/cloning-fidelity|Theorem 2 channel]] into $\mathcal H_\Lambda$. The decoder samples a sector from the known spectrum-dependent distribution, applies its reverse channel, and reconstructs the physical source registers. It does **not** require the encoder to retain the measured label. Explicit replacement channels handle atypical sectors, making the maps CPTP on every input.

These are the definitions [FreeEntropy.SchurWeyl.mixedEncoder](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/PhysicalCloningChannels.lean#L64) and [FreeEntropy.SchurWeyl.mixedDecoder](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/PhysicalCloningChannels.lean#L69).

### Error and memory

Compare both directions with the same target orbit state $\tau_{U,n}$. Contractivity and the triangle inequality give

$$
T\bigl(\mathcal D_n\mathcal E_n(\rho_U^{\otimes n}),\rho_U^{\otimes n}\bigr)
\le T\bigl(\mathcal E_n(\rho_U^{\otimes n}),\tau_{U,n}\bigr)
+T\bigl(\mathcal D_n(\tau_{U,n}),\rho_U^{\otimes n}\bigr),
$$

where $T(A,B)=\frac12\|A-B\|_1$. Each term is bounded by the largest typical channel error plus the atypical mass. Theorem 2 gives the trace-distance estimate directly: $C_{d,x}D/(b_\lambda+1)=O(\log n/\sqrt n)$. [[results/lemmas/sanov-theorem|Physical concentration]] makes the tail negligible. Covariance makes these comparison estimates uniform in $U$; [FreeEntropy.SchurWeyl.mixed_comparison_error_eventually](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/PhysicalCloningAccuracy.lean#L41) proves the actual estimates.

The memory dimension is the actual dimension of $\mathcal H_\Lambda$. The checked [[results/lemmas/weyl-dimension-asymptotic|Weyl dimension and padded-target limit]] give $\log_2\dim\mathcal H_\Lambda-L_{d,r}(n,x)\to0$. For pure states the expression simplifies to $(d-1)\log_2 n-\log_2((d-1)!)+o(1)$.

## Formalization Scope

The final theorem takes only `FixedSpectrum d r`. Representation existence, physical decomposition, dimensions, concentration, channel construction, and the error estimates are proved dependencies, not supplied hypotheses. The [[formalization|verification guide]] and [natural-language map](https://github.com/JWang226/QMDL/blob/main/metadata/natural-language-map.json) link the complete chain.

Earlier wiki versions called achievability “Theorem 2” and used $O(n^{-1/4+\varepsilon})$ from a fidelity-to-trace-distance conversion. Those describe an older proof route in the project sources. The current Article's main Theorem 1 and Lean endpoint use the direct $O(\log n/\sqrt n)$ estimate.

## Dependencies

- [[results/cloning-fidelity|Theorem 2: finite cloning accuracy]]
- [[concepts/schur-weyl-duality|Physical irreducible-sector decomposition]]
- [[definitions/typical-set|Typical rows]] and [[results/lemmas/sanov-theorem|concentration]]
- [[results/lemmas/weyl-dimension-asymptotic|Exact dimension and asymptotic memory]]

## Used By

- [[concepts/quantum-minimum-description-length|Quantum minimum description length]]
- [[results/converse|Theorem 1 converse]], through the two comparison channels
