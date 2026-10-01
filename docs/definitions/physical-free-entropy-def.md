# Physical Free Entropy (Formal Definition)

**Source:** current [[Letter]], `eq:free_phys_def`, `eq:free_phys`, and `eq:degenerate_free_ent` in [letter.tex](https://github.com/JWang226/QMDL/blob/main/letter.tex). All logarithms are base two.

## Statement

Let $\rho$ be a $d\times d$ Hermitian matrix with ordered eigenvalues $p_1\ge\cdots\ge p_d$. Define

$$
\Omega_\varepsilon=\{X\in M_d^{\mathrm{s.a.}}:\|\lambda(X)-p\|_2\le\varepsilon\},
\qquad
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=\log_2\frac{\operatorname{Vol}(\Omega_\varepsilon)}
{\operatorname{Vol}(B_\varepsilon^{d^2})}.
$$

Here $\lambda(X)$ is the ordered eigenvalue list, and both volumes use the Hilbert–Schmidt Euclidean metric on the **full Hermitian matrix space**. The tube may contain matrices that are not density operators. The definition applies at every $\varepsilon>0$; it does not require a spectral-gap condition.

The Hoffman–Wielandt inequality, with equality after aligning eigenbases, gives

$$\min_U\|X-U\rho U^\dagger\|_2=\|\lambda(X)-p\|_2.$$

Thus $\Omega_\varepsilon$ is exactly the radius-$\varepsilon$ neighborhood of the unitary orbit. It contains the ball centered at $\rho$, so $\chi_{\mathrm{phy}}\ge0$. For a scalar matrix the orbit is a point and the entropy is exactly zero.

## Volume Ratio and Covering Numbers

The current Letter defines a **volume ratio**, not an exact minimum covering number. At fixed $d$, its logarithm and the logarithm of a suitable covering number agree up to $O(1)$ as $\varepsilon\to0$. The volume convention fixes that otherwise ambiguous additive constant, which matters for the Letter's QMDL relation.

## Small-Resolution Expansion

Let the distinct eigenvalues have multiplicities $g_a$, including any zero eigenspace, and put

$$\kappa=\sum_a g_a^2,\qquad N_\rho=d^2-\kappa.$$

Let $g$ be the smallest gap between **distinct** eigenvalues, with $g=\infty$ for a scalar matrix. For $\varepsilon<g/2$, the Letter derives

$$
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=N_\rho\log_2\varepsilon^{-1}
+\chi_{\mathrm{reg}}(\rho)+c(d,(g_a))
+O_d(\varepsilon^2/g^2),
$$

where

$$
\begin{aligned}
 c(d,(g_a))={}&\frac{N_\rho}{2}\log_2 2
+\log_2\frac{\Gamma(d^2/2+1)}{\Gamma(\kappa/2+1)}\\
&+\sum_a\sum_{k=1}^{g_a-1}\log_2(k!)
-\sum_{k=1}^{d-1}\log_2(k!).
\end{aligned}
$$

The small-gap condition controls the expansion and prevents different spectral clusters from crossing. Eigenvalues within a repeated cluster can still split, so matrices in the tube need not have the same stabilizer as $\rho$.

For a qubit with fixed gap $h=2p-1>0$,

$$\chi_{\mathrm{phy}}(\rho;\varepsilon)
=2\log_2\varepsilon^{-1}+2\log_2 h+2+O(\varepsilon^2/h^2).$$

This is an asymptotic effective cell count, not an exact number of distinguishable states.

## Role in QMDL and Formalization

For the Letter's attaining codes with distinct nonzero eigenvalues,

$$|M_n|=\tfrac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1).$$

The resolution $n^{-1}$ belongs to this volume comparison; it is not an eigenbasis-estimation accuracy claim. The [[Article]] and Lean endpoints prove the underlying memory formula. The tube-volume calculation and this free-entropy identification are additional Letter results, outside the current two-theorem formalization.

## Used By

- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[definitions/regularized-free-entropy|Regularized Free Entropy]]
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[open-questions/degenerate-spectrum|Repeated positive eigenvalues]]
