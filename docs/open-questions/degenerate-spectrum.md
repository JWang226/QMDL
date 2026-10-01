# QMDL for Repeated Positive Eigenvalues

**Source:** current [[Letter]], End Matter “Free entropy of density operators with a degenerate spectrum,” `eq:degenerate_free_ent`, `eq:rank_def_qmdl`, and its final paragraph; current [[Article]], `thm:qmdl`.
**Status:** General-multiplicity entropy geometry is derived in the Letter. QMDL for repeated positive eigenvalues remains conjectural and is outside the current Lean theorem.

## What Is Already Included

The current Article and `Theorem1Complete` assume strictly decreasing **positive** eigenvalues $x_1>\cdots>x_r>0$. They include $r<d$, repeated zero eigenvalues, pure states ($r=1$), and $d=1$. Those cases are not open formalization gaps.

The extension considered here is a collision among positive eigenvalues, such as $x_i=x_{i+1}>0$. The fully maximally mixed state has a singleton orbit and needs no basis memory, but that elementary endpoint does not establish a general theorem for intermediate degeneracy patterns.

## Geometry Is Already Derived

For distinct eigenvalues $p_a$ with multiplicities $g_a$, including the zero eigenspace, the Letter derives

$$\chi_{\mathrm{phy}}(\rho;\varepsilon)
=\left(d^2-\sum_a g_a^2\right)\log_2\varepsilon^{-1}
+2\sum_{a<b}g_ag_b\log_2|p_a-p_b|
+c(d,(g_a))+O_d(\varepsilon^2/g^2).$$

The explicit constant and volume convention are on the [[definitions/physical-free-entropy-def|definition page]]. This geometric result is broader than the operational compression theorem. The Letter explicitly expects, rather than proves, the QMDL relation for arbitrary multiplicities.

## Why the Current Estimates Change

The supported [[definitions/edge-gap|row gaps]] of typical partitions grow linearly only across distinct eigenvalues. At a repeated positive eigenvalue this uniform lower bound is unavailable. Also, the ratio $q_x=\max_{i<r}x_{i+1}/x_i$ can reach one, so the present mean-depth and uniform canonical-gap bounds no longer provide spectrum-dependent positive constants.

The actual physical decomposition, CPTP channel construction, and concentration proofs are established. Extending the final asymptotic estimates to repeated positive spectra requires an argument adapted to the smaller unitary orbit, rather than filling a missing Schur decomposition premise.

## Expected Leading Term

For distinct eigenvalues with multiplicities $g_1,\ldots,g_k$, **including the zero eigenspace if present**, the orbit is

$$U(d)/(U(g_1)\times\cdots\times U(g_k))$$

and its real dimension is $d^2-\sum_a g_a^2$. The Letter conjectures the extension of its operational relation, whose expected leading memory cost is

$$|M_n|=\frac{d^2-\sum_a g_a^2}{2}\log n+O(1).$$

This broader formula and its additive constant are not conclusions of the current Lean endpoint.

## Converse Issue

The current approximate converse uses a simple top eigenvalue separated by a uniform positive gap, rather than the older wiki's Lagrange-interpolation/Koashi–Imoto argument. Repeated positive spectra can destroy that simple-top-gap input. A suitable block version or a different quantitative memory argument would be needed for the general extension.

## Related

- [[proof-structure]]
- [[concepts/flag-manifold|Flag Manifold]]
- [[definitions/edge-gap|Supported Row Gaps]]
- [[results/converse|Converse (Article Theorem 1)]]
- [[open-questions/free-entropy-conjecture|Broader Free-Entropy Questions]]
