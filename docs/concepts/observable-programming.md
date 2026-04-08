# Observable Programming

**Appears in:** Notes (Sec. 9)

## Intuition

Given a Hermitian observable $H$ (think: a measurement apparatus), can you store a "program" for it in a quantum memory and later use a universal processor to perform $H$'s spectral measurement on any input state? This extends [[concepts/unitary-programming|Unitary Programming]] from unitaries to observables.

## Two Variants

### 1. Spectral Measurement Programming
Program the full spectral (projective) measurement of $H$. The observable $H$ with distinct eigenvalues $h_1, \ldots, h_m$ and multiplicities $g_1, \ldots, g_m$ defines a measurement $\{P_a\}$ where $P_a$ projects onto the $g_a$-dimensional eigenspace.

**Result:** The optimal program dimension satisfies:
$$\log D = \frac{d^2 \cdot \delta(H)}{2} \log(1/\varepsilon) + O(1)$$

where $\delta(H) = 1 - \sum_a g_a^2 / d^2$ is the [[concepts/free-entropy-dimension|Free Entropy Dimension]].

This works by reduction to unitary programming on the flag manifold $U(d)/(U(g_1) \times \cdots \times U(g_m))$.

### 2. Expectation Value Programming (Notes, Sec. 9)
Program only the ability to estimate $\mathrm{Tr}[H\rho]$ for any input $\rho$. This is a strictly weaker task than spectral measurement programming, since knowing $\mathrm{Tr}[H\rho]$ for all $\rho$ determines $H$ up to an additive constant, but implementing the expectation estimation does not require implementing the full projective measurement.

**Status:** Achievability follows from spectral measurement programming (if you can implement the full measurement, you can certainly compute the expectation value). The **converse is open** -- it is not known whether the same rate $\frac{d^2 \delta(H)}{2}\log(1/\varepsilon)$ is a lower bound for the weaker task. See [[open-questions/observable-expectation-converse|Open: Observable Expectation Converse]] for a discussion of why the spectral measurement converse does not directly apply.

## Related

- [[concepts/unitary-programming|Unitary Programming]] -- the unitary analogue
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- governs the leading rate
- [[open-questions/observable-expectation-converse|Open: Observable Expectation Converse]]
