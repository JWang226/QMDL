# Error Scaling Beyond the Current Bound

**Source:** Historical [[Notes]] discussion; current [[Article]], `thm:achievability`, `thm:main`.
**Status:** Earlier exponent bottleneck resolved; sharp finite-error tradeoffs remain outside the proved statement.

## Current Result

The current Article and the Lean endpoint `FreeEntropy.theorem1_achievability` prove worst-case trace-distance error

$$\delta_n=O\!\left(\frac{\log n}{\sqrt n}\right)$$

with memory cost $L_{d,r}(n,x)+o(1)$, for a fixed spectrum with strictly decreasing positive eigenvalues. Rank-deficient and rank-one sources are included.

The Notes' older $O(n^{-1/4+\varepsilon})$ route passed through a fidelity estimate and a square-root conversion. It is not the current error bound or an unclosed formalization gap.

## Why the Bound Improved

The current cloning theorem controls trace distance directly:

$$\frac12\|\mathcal C_{\mu\to\nu}(\rho_\mu)-\rho_\nu\|_1
\le C_{d,x}\frac{\|\nu-\mu\|_1}{b_\mu+1},$$

with the same bound in reverse. The proof averages localized Casimir **trace deficits**, using shallow multiplicity equality and a bounded mean root depth. Typical rows have $b_\mu=\Omega(n)$ and padded-target distance $O(\sqrt n\log n)$. The actual atypical mass is negligible. No Davis–Kahan hypothesis or assumed concentration estimate remains in the final endpoint.

## What Is Not Claimed

The current theorem does not establish the optimal error at every fixed memory budget, nor a general $O(n^{-1/2})$ bound without the logarithmic factor at the same $L_{d,r}(n,x)+o(1)$ memory precision. Whether a different protocol or more refined choice of window improves that tradeoff is a separate question. The older Notes' proposed approaches should be read in that historical context.

## Related

- [[proof-structure]]
- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]]
- [[results/achievability|Achievability (Article Theorem 1)]]
- [[concepts/casimir-operator|Casimir Operator]]
- [[concepts/ych-scheme|YCH Scheme]]
