# Regularized Free Entropy

**Source:** current [[Letter]], `eq:reg_free_ent` and `eq:degenerate_free_ent` in [letter.tex](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex).

## Statement

For eigenvalues $p_1,\ldots,p_d$, the Letter uses the **unnormalized** convention

$$\chi_{\mathrm{reg}}(\rho)=2\sum_{i<j,\ p_i\ne p_j}\log_2|p_i-p_j|.$$

Equivalently, if the distinct eigenvalues are $p_1>\cdots>p_m$ with multiplicities $g_1,\ldots,g_m$,

$$\chi_{\mathrm{reg}}(\rho)=2\sum_{a<b}g_ag_b\log_2|p_a-p_b|.$$

The normalized logarithmic energy is $d^{-2}\chi_{\mathrm{reg}}$, a different quantity. Older wiki formulas included this factor in the definition; that is not the current Letter's convention. Repeated eigenvalues, including repeated zeros, contribute no coincident-pair terms.

## Relation to Physical Free Entropy

With $N_\rho=d^2-\sum_a g_a^2$ and smallest distinct spectral gap $g$,

$$
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=N_\rho\log_2\varepsilon^{-1}
+\chi_{\mathrm{reg}}(\rho)+c(d,(g_a))
+O_d(\varepsilon^2/g^2).
$$

The constant is given on the [[definitions/physical-free-entropy-def|physical free entropy definition page]]. For density matrices, all nonzero gaps lie in $(0,1]$, so $\chi_{\mathrm{reg}}\le0$. Equality includes pure states **and scalar states**, whose sum has no terms.

As a pair of distinct eigenvalues approaches a collision, its logarithmic contribution diverges negatively. At the exact collision, that pair is omitted and the multiplicities and orbit dimension change. Thus this regularized quantity is not continuous across strata, and the fixed-gap expansion is not uniform through a collision.

For a qubit with eigenvalues $p,1-p$, $p>1/2$,

$$\chi_{\mathrm{reg}}(\rho)=2\log_2(2p-1).$$

At $p=0.7$ this is approximately $-2.644$ bits. At the exactly maximally mixed state it is zero by the empty-sum convention.

## Role in QMDL

For rank $r$ with distinct positive eigenvalues, the Letter and [[Article]] give an attaining sequence with

$$
|M_n|=\frac{r(2d-r-1)}2\log_2 n
+\frac12\chi_{\mathrm{reg}}(\rho)
-\sum_{k=d-r}^{d-1}\log_2(k!)+o(1).
$$

Here $|M_n|=\log_2\dim M_n$ already denotes a logarithmic cost. The formula for general repeated positive spectra is a conjectural extension; the general geometric entropy expansion does not itself prove a compression theorem. The current Lean endpoints prove the displayed memory formula in the distinct-positive-spectrum case, without formalizing the entropy definition or its volume calculation.

## Used By

- [[concepts/free-entropy|Free Entropy]]
- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[results/achievability|Achievability]] and [[results/converse|converse]]
- [[open-questions/degenerate-spectrum|Repeated positive eigenvalues]]
