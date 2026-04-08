# Tail Mass (Lemma 8)

**Label:** `lem:tail` (Article and Notes)
**Source:** Article line ~1624 (stated), ~2577 (proved); Notes line ~759

## Statement

The tail mass of the GL irrep at depth $T$:

$$\varepsilon_\mu(T) = \sum_{|\delta| > T} p_\mu(\delta) \cdot m_\mu(\delta) = O\left(T^\kappa \cdot \mathfrak{p}^T\right)$$

where:
- $\kappa = r(r-1)/2 - 1$
- $\mathfrak{p} = \max_i(x_{i+1}/x_i) < 1$ (the largest eigenvalue ratio)
- $p_\mu(\delta) = x^{\mu-\delta}/s_\mu(x)$ is the probability of weight $\mu - \delta$
- $m_\mu(\delta) = K_{\mu, \mu-\delta}$ is the Kostka number (multiplicity)

For rank $r = 1$, there are no positive roots, so $\varepsilon_\mu(T) = 0$ trivially.

## Intuition

Deep weight spaces (far from the highest weight) contribute exponentially little to the state. The decay rate $\mathfrak{p}^T$ is governed by the spectral gap: a larger gap between consecutive eigenvalues means the state is more concentrated near the highest weight. The polynomial prefactor $T^\kappa$ comes from the combinatorial growth of weight multiplicities at depth $T$, but this polynomial growth is overwhelmed by the exponential decay. This allows the [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] proof to truncate the weight sum at a manageable depth $T = O(n^\varepsilon)$ while losing only superpolynomially small mass.

## Proof Sketch

**Main idea:** Each step away from the highest weight costs a factor $\leq \mathfrak{p} = \max_i(x_{i+1}/x_i) < 1$ in probability, giving $p_\mu(\delta) \leq \mathfrak{p}^{|\delta|}$. The total multiplicity at depth $t$ grows polynomially as $O(t^\kappa)$ (bounded via Kostant's partition function and generating functions for type-$A$ root systems). Polynomial times exponential decay sums to $O(T^\kappa \mathfrak{p}^T)$.

---

### Extended Proof

### Step 1: Bound Individual Weights by $\mathfrak{p}^{|\delta|}$

Write the offset in the simple-root basis: $\delta = \sum_{i=1}^{r-1} c_i \alpha_i$ with $c_i \geq 0$ and $|\delta| = \sum c_i$. Since $\alpha_i = e_i - e_{i+1}$:

$$x^{\mu - \delta} = x^\mu \prod_{i=1}^{r-1} \left(\frac{x_{i+1}}{x_i}\right)^{c_i} \leq x^\mu \cdot \mathfrak{p}^{|\delta|}$$

The coefficient of $x^\mu$ in $s_\mu(x)$ is 1 (the highest-weight monomial), so $s_\mu(x) \geq x^\mu$. Therefore:

$$p_\mu(\delta) = \frac{x^{\mu-\delta}}{s_\mu(x)} \leq \mathfrak{p}^{|\delta|}$$

This is the key exponential bound: each step away from the highest weight costs a factor of at most $\mathfrak{p} < 1$.

### Step 2: Bound Total Multiplicity via Kostant's Partition Function

Define the total multiplicity at depth $t$: $D_\mu(t) = \sum_{|\delta| = t} m_\mu(\delta)$.

Since $\mathcal{H}_\mu$ is a quotient of the Verma module $M(\mu)$, every weight multiplicity is bounded above by Kostant's partition function: $m_\mu(\delta) \leq \mathcal{P}_r(\delta)$, where $\mathcal{P}_r(\delta)$ counts decompositions of $\delta$ into non-negative integer combinations of positive roots of type $A_{r-1}$.

Hence $D_\mu(t) \leq A_r(t) := \sum_{|\delta|=t} \mathcal{P}_r(\delta)$.

### Step 3: Generating Function Analysis

The generating function of $A_r(t)$ factors over positive roots (since height is additive):

$$\sum_{t \geq 0} A_r(t) q^t = \prod_{\alpha \in \Phi_r^+} \frac{1}{1 - q^{|\alpha|}}$$

For type $A_{r-1}$, there are exactly $r - h$ positive roots of height $h$ (for $h = 1, \ldots, r-1$). So:

$$\sum_{t \geq 0} A_r(t) q^t = \prod_{h=1}^{r-1} \frac{1}{(1 - q^h)^{r-h}}$$

This has a pole of order $N = |\Phi_r^+| = r(r-1)/2$ at $q = 1$. Since all coefficients are non-negative, we can bound coefficientwise by replacing $q^h \to q$:

$$A_r(t) \leq [q^t](1-q)^{-N} = \binom{t + N - 1}{N - 1} \leq C_r (t+1)^{N-1} = C_r(t+1)^\kappa$$

where $\kappa = N - 1 = r(r-1)/2 - 1$ and $C_r$ depends only on $r$.

### Step 4: Combine

$$\varepsilon_\mu(T) = \sum_{|\delta| > T} p_\mu(\delta) m_\mu(\delta) \leq \sum_{t > T} D_\mu(t) \mathfrak{p}^t \leq C_r \sum_{t > T} (t+1)^\kappa \mathfrak{p}^t$$

Substituting $t = T + 1 + s$ with $s \geq 0$:

$$\sum_{t > T} (t+1)^\kappa \mathfrak{p}^t = \mathfrak{p}^{T+1} \sum_{s \geq 0} (T + s + 2)^\kappa \mathfrak{p}^s \leq \mathfrak{p}^{T+1} (T+2)^\kappa \underbrace{\sum_{s \geq 0} (s+2)^\kappa \mathfrak{p}^s}_{< \infty \text{ since } \mathfrak{p} < 1}$$

The series converges because $0 < \mathfrak{p} < 1$. Therefore:

$$\varepsilon_\mu(T) = O(T^\kappa \mathfrak{p}^T)$$

**Application:** When $T = O(n^\varepsilon)$, this becomes $O(n^{\varepsilon\kappa} \mathfrak{p}^{n^\varepsilon})$, which is superpolynomially small -- far below the polynomial error $O(d(\mu,\nu)/n^{1-\varepsilon})$ from the perturbation bound.

## Dependencies

- Kostant's partition function bounds (Verma module weight multiplicities)
- Generating function analysis for type $A_{r-1}$ root systems
- Strict positivity of eigenvalue gaps ($x_1 > \cdots > x_r > 0$)

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- Step 6 (tail truncation at depth $T = O(n^\varepsilon)$)
