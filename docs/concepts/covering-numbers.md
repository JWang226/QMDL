# Covering Numbers (Kolmogorov $\varepsilon$-Entropy)

**Appears in:** [[Letter]] (the footnote to `eq:free_phys_def`); historical [[Notes]] (Sec. 2.2).

## Definition

For a subset $\Omega$ of a metric space, the $\varepsilon$-covering number $N(\Omega,\varepsilon)$ is the minimum number of radius-$\varepsilon$ balls needed to cover $\Omega$. Its logarithm is the Kolmogorov $\varepsilon$-entropy. All logarithms here are binary.

This is a geometric measure of resolution: it counts how many descriptions suffice to locate a point to the specified accuracy. It is distinct from algorithmic [[concepts/kolmogorov-complexity|Kolmogorov complexity]].

## The Letter's Volume Convention

The current Letter defines [[concepts/physical-free-entropy|physical free entropy]] by an ambient volume ratio, not an exact covering number. For the fixed-spectrum unitary orbit $\mathcal O_\rho$, let

$$\Omega_\varepsilon=\{X=X^\dagger:\operatorname{dist}_{\mathrm{HS}}(X,\mathcal O_\rho)\le\varepsilon\}.
\qquad
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=\log\frac{\operatorname{Vol}(\Omega_\varepsilon)}{\operatorname{Vol}(B_\varepsilon^{d^2})}.$$

The distance and reference ball use the Hilbert–Schmidt norm on the full real vector space of Hermitian matrices. The tube includes matrices that need not be positive or trace one. Equivalently, its ordered eigenvalue list lies within Euclidean distance $\varepsilon$ of the prescribed list.

At fixed dimension, the Letter notes that the logarithmic volume ratio and logarithmic covering count agree up to $O(1)$ as $\varepsilon\to0$. That bounded ambiguity matters when comparing additive constants. The volume convention fixes the explicit constant in the Letter's QMDL relation; an unspecified covering convention does not.

## Dimension and Resolution

For a Euclidean ball of fixed radius $R$, volume bounds give

$$\log N(B^m(R),\varepsilon)=m\log(R/\varepsilon)+O_m(1).$$

For an orbit whose distinct eigenvalues have multiplicities $g_a$, the analogous leading coefficient is its real dimension $N_\rho=d^2-\sum_a g_a^2$. The Letter's stronger tube-volume calculation gives

$$\chi_{\mathrm{phy}}(\rho;\varepsilon)
=N_\rho\log\varepsilon^{-1}+\chi_{\mathrm{reg}}(\rho)
+C(d,(g_a))+O_d(\varepsilon^2/g^2),$$

where $g$ is the smallest gap between distinct eigenvalues and $\varepsilon<g/2$. The result is labeled `eq:degenerate_free_ent` in the End Matter. These geometric calculations are not part of the current Lean proof of the Article's compression theorems; see [[proof-structure]].

The Letter evaluates this quantity at $\varepsilon=n^{-1}$ in its half-entropy memory formula. The separate statistical scale $n^{-1/2}$ describes local distinguishability of orbit states and should not be substituted into that formula.

## Related

- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[definitions/physical-free-entropy-def|Physical Free Entropy (Formal Definition)]]
- [[concepts/free-entropy-dimension|Free Entropy Dimension]]

## References

- `KolmogorovTikhomirov1961`: A. N. Kolmogorov and V. M. Tikhomirov, "$\varepsilon$-entropy and $\varepsilon$-capacity of sets in functional spaces."
- `Kolmogorov1963`: Theory of transmission of information.
