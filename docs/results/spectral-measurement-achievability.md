# Spectral Measurement Programming (Achievability)

**Source:** Notes Sec. 9.2.1 (line ~1693)

## Statement

For a Hermitian observable $H = \sum_{a=1}^k E_a P_a$ on $\mathbb{C}^d$ with $k$ distinct eigenvalues and eigenspace multiplicities $g_1, \ldots, g_k$, the spectral measurement $\{P_a\}$ (projectors onto eigenspaces) can be programmed with error $\varepsilon$ using a program of dimension:

$$\log D = \frac{d^2 \cdot \delta(H)}{2}\log(1/\varepsilon) + O(1)$$

where $\delta(H) = 1 - \sum_a g_a^2/d^2$ is the [[concepts/free-entropy-dimension|Free Entropy Dimension]]. The eigenvalues $\{E_a\}$ are assumed to be provided classically and are not part of the program.

## Intuition

Programming a projective measurement $\{P_a\}$ is equivalent to programming the change-of-basis unitary that diagonalizes $H$. But we do not need to program a full $U(d)$ unitary -- we only need the unitary modulo phases within each eigenspace. This reduces the problem to programming unitaries on the [[concepts/flag-manifold|Flag Manifold]], which has fewer degrees of freedom than $U(d)$ itself.

## Proof Sketch

**Main idea:** Programming the spectral measurement $\{P_a\}$ reduces to programming the change-of-basis unitary modulo the stabilizer $U(g_1) \times \cdots \times U(g_k)$. The relevant parameter space is the flag manifold with $f = d^2 - \sum g_a^2 = d^2 \delta(H)$ real dimensions. Applying sine-state programming on this $f$-parameter family gives cost $(f/2)\log(1/\varepsilon) + O(1)$.

---

### Extended Proof

**Step 1: Spectral measurement depends only on the eigenbasis.** Given $H = \sum_a E_a P_a$, the spectral measurement is the POVM $\{P_a\}$. This depends only on the eigenspaces (the $P_a$'s), not on the eigenvalues $E_a$. We want a program $\sigma_H$ and a universal processor such that:

$$\mathrm{Tr}\,\rho \otimes \sigma_H \cdot \Pi_a \approx \mathrm{Tr}\, P_a \rho, \quad \forall\, \rho$$

**Step 2: Reduce to a change-of-basis unitary.** Any projective measurement can be implemented as: (i) apply a unitary $U$ to rotate the eigenbasis to the computational basis, (ii) measure in the computational basis. Concretely, if $P_a = U^\dagger (\sum_{i \in I_a} |i\rangle\langle i|) U$ where $\{I_a\}$ partitions $[d]$ with $|I_a| = g_a$, then any $\varepsilon$-programming scheme $(\sigma_U, \mathcal{P})$ for $U$ yields a measurement programming scheme $(\sigma_H = \sigma_U, \{\mathcal{P}^\dagger(|i\rangle\langle i|)\}_i)$ with the same error.

**Step 3: Identify the relevant coset (flag manifold).** We do not need $U$ to be a specific unitary -- we only need its action modulo the stabilizer of the computational-basis eigenspaces. Two unitaries $U$ and $U'$ give the same spectral measurement if and only if $U' = U \cdot \mathrm{diag}(V_1, \ldots, V_k)$ where $V_a \in U(g_a)$. Thus the space of distinct measurements is the [[concepts/flag-manifold|Flag Manifold]]:

$$\mathcal{F} = U(d) \big/ \bigl(U(g_1) \times \cdots \times U(g_k)\bigr)$$

**Step 4: Count the degrees of freedom.** The real dimension of this flag manifold is:

$$f = \dim_{\mathbb{R}} \mathcal{F} = d^2 - \sum_{a=1}^k g_a^2 = d^2 \cdot \delta(H)$$

For the non-degenerate case ($k = d$, all $g_a = 1$), this gives $f = d^2 - d$, and $\delta(H) = 1 - 1/d$. For a maximally degenerate observable ($k = 1$), $f = 0$ and no program is needed.

**Step 5: Apply sine-state programming.** The flag manifold $\mathcal{F}$ is an $f$-parameter family of unitaries (modulo the stabilizer). Applying the [[results/sine-state-programming|Sine-State Programming Proposition]] with $f = d^2 \cdot \delta(H)$ real parameters:

$$\log D = \frac{f}{2}\log(1/\varepsilon) + O(1) = \frac{d^2 \cdot \delta(H)}{2}\log(1/\varepsilon) + O(1)$$

This matches $\chi_{\mathrm{phy}}(H; \varepsilon)$ at leading order, where the leading coefficient is controlled by the free entropy dimension.

**Remark on the non-degenerate case.** When $H$ has all distinct eigenvalues, the coset is $U(d)/(U(1)^d)$ with $f = d^2 - d$ and $\delta(H) = (d^2 - d)/d^2$. The program cost is $(d^2 - d)/2 \cdot \log(1/\varepsilon) + O(1)$, which is strictly smaller than the cost of programming a full $U(d)$ unitary (which would be $d^2/2 \cdot \log(1/\varepsilon)$).

## Dependencies

- [[results/sine-state-programming|Sine-State Programming Proposition]] -- the concrete programming protocol
- [[results/estimation-programming-lemma|Estimation-Programming Lemma]] -- used via the sine-state chain
- [[concepts/flag-manifold|Flag Manifold]] -- the parameter space of spectral measurements
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- $\delta(H) = 1 - \sum_a g_a^2/d^2$, which controls the leading-order cost

## Used By

- [[concepts/observable-programming|Observable Programming]] -- spectral measurement programming is one formulation
- [[results/observable-expectation-achievability|Observable Expectation Programming (Achievability)]] -- as an upper bound (the harder task subsumes the easier one)
- [[results/spectral-measurement-converse|Spectral Measurement Programming (Converse)]] -- matched at leading order
