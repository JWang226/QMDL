# QMDL for Repeated Positive Eigenvalues

**Source:** [[Letter]] Appendix B; current [[Article]] fixed-spectrum hypotheses.
**Status:** General repeated-positive-spectrum extension is outside the current formalized theorem.

## What Is Already Included

The current Article and `Theorem1Complete` assume strictly decreasing **positive** eigenvalues $x_1>\cdots>x_r>0$. They include $r<d$, repeated zero eigenvalues, pure states ($r=1$), and $d=1$. Those cases are not open formalization gaps.

The extension considered here is a collision among positive eigenvalues, such as $x_i=x_{i+1}>0$. The fully maximally mixed state has a singleton orbit and needs no basis memory, but that elementary endpoint does not establish a general theorem for intermediate degeneracy patterns.

## Why the Current Estimates Change

The supported [[definitions/edge-gap|row gaps]] of typical partitions grow linearly only across distinct eigenvalues. At a repeated positive eigenvalue this uniform lower bound is unavailable. Also, the ratio $q_x=\max_{i<r}x_{i+1}/x_i$ can reach one, so the present mean-depth and uniform canonical-gap bounds no longer provide spectrum-dependent positive constants.

The actual physical decomposition, CPTP channel construction, and concentration proofs are established. Extending the final asymptotic estimates to repeated positive spectra requires an argument adapted to the smaller unitary orbit, rather than filling a missing Schur decomposition premise.

## Expected Leading Term

For distinct eigenvalues with multiplicities $g_1,\ldots,g_k$, **including the zero eigenspace if present**, the orbit is

$$U(d)/(U(g_1)\times\cdots\times U(g_k))$$

and its real dimension is $d^2-\sum_a g_a^2$. The Letter motivates the expected leading memory cost

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
