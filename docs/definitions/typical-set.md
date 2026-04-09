# Typical Set of Young Diagrams

**Source:** Article line ~869

## Statement

For eigenvalue vector $p = (p_1, \ldots, p_r, 0, \ldots, 0)$ and parameter $\xi_n = \sqrt{2n}\log n + 1$, the **typical set** is:

$$T_{p,n} = \left\{\lambda \vdash n, \ell(\lambda) \leq d : d(\lambda/n, p) \leq \xi_n / \sqrt{n}\right\}$$

where $d(\lambda/n, p) = \sum_i |\lambda_i/n - p_i|$ is the $L^1$ distance.

## Intuition

The typical set contains Young diagrams whose normalized shape $\lambda/n$ is close to the eigenvalue distribution $p$. By [[results/sanov-theorem|Sanov's Theorem (Lemma 12)]], the probability of being outside $T_{p,n}$ is exponentially small: $\Pr[\lambda \notin T_{p,n}] \leq (n+1)^{r(r+1)/2} e^{-2n\xi_n^2/n}$.

The padding $\xi_n = O(\sqrt{n}\log n)$ is chosen to be large enough that atypical sectors are negligible, but small enough that $\xi_n/\sqrt{n} \to 0$.

### Why $\xi_n = 2\sqrt{n\Delta_n/2} + 1$

The padding parameter $\xi_n$ must be chosen so that the target representation $\Lambda^*$ strictly dominates every typical $\lambda$. The achievability proof constructs $\Lambda^*_i = \lceil n x_i + (r-i)\xi_n \rceil$, and requires the dominance condition:

$$\Lambda^*_i - \Lambda^*_{i+1} \geq \lambda_i - \lambda_{i+1}$$

for all typical $\lambda$. In the worst case, adjacent rows fluctuate in opposite directions, giving $\lambda_i - \lambda_{i+1} \leq n(x_i - x_{i+1}) + 2\epsilon_n$ where $\epsilon_n = \sqrt{n\Delta_n/2}$ is the maximum fluctuation bound from the typical set definition. Meanwhile, the guaranteed gap of $\Lambda^*$ is at least $n(x_i - x_{i+1}) + \xi_n - 1$ (accounting for ceiling rounding). After the macroscopic $n(x_i - x_{i+1})$ terms cancel, we need:

$$\xi_n - 1 \geq 2\epsilon_n$$

Setting $\xi_n = 2\epsilon_n + 1 = 2\sqrt{n\Delta_n/2} + 1$ is the **tightest** sub-extensive buffer that absorbs both the worst-case statistical fluctuations *and* the discrete rounding error from the ceiling function. This is the "Goldilocks" choice: just barely large enough to guarantee dominance, but not so large as to inflate the memory cost beyond $o(1)$.

## Numerical Example: $d = 2$, $n = 10000$

Consider a qubit with spectrum $p = (0.7, 0.3)$ and $n = 10000$ copies.

**Parameters:**
- $r = 2$ (rank)
- $\Delta_n = (\log n)^2 = (\log 10000)^2 \approx (13.3)^2 \approx 177$ (using $\log_2$; in the article, $\Delta_n = (\log n)^2$ with natural log gives $\Delta_n \approx 85$)
- Using natural log: $\epsilon_n = \sqrt{n\Delta_n/2} = \sqrt{10000 \cdot 85/2} \approx \sqrt{425000} \approx 652$
- $\xi_n = 2 \cdot 652 + 1 = 1305$

**Typical set:** A Young diagram $\lambda = (\lambda_1, \lambda_2)$ with $\lambda_1 + \lambda_2 = 10000$ is typical if:

$$|\lambda_1 - 7000| \leq 652 \quad \text{and} \quad |\lambda_2 - 3000| \leq 652$$

So the typical range is $\lambda_1 \in [6348, 7652]$, which contains about 1305 distinct Young diagrams out of the 10001 possible partitions of 10000 into at most 2 parts.

**Target representation:**
- $\Lambda^*_1 = \lceil 7000 + 1 \cdot 1305 \rceil = 8305$
- $\Lambda^*_2 = \lceil 3000 + 0 \cdot 1305 \rceil = 3000$
- Note: $|\Lambda^*| = 11305 \neq 10000$ -- the target is *not* a partition of $n$.

**Tail probability:** $\Pr[\lambda \notin T_{p,n}] \leq (10001)^3 e^{-85} \approx 10^{12} \cdot 10^{-37} \approx 10^{-25}$, which is astronomically small.

## Connection to Proof Architecture

The typical set plays a dual role:
- In the **achievability** proof, it defines the set of Young diagrams for which the [[definitions/generalized-cloning-map-def|Generalized Cloning Map]] achieves high fidelity. Atypical $\lambda$ contribute at most $\delta_{\mathrm{tail}} \leq (n+1)^{r(r+1)/2} e^{-\Delta_n}$ to the error.
- In the **converse** proof, the typical set $\mathcal{T}_{p,n}$ intersects the "good set" $\mathcal{G}_n$ (where the sector codes perform well), guaranteeing that at least one typical $\lambda$ has a well-performing code. The memory lower bound then follows from the Weyl dimension of this typical irrep.

## Used By

- [[results/achievability|Achievability (State Compression)]]
- [[results/converse|Converse (State Compression)]]

## External References

- [Typical set (Wikipedia)](https://en.wikipedia.org/wiki/Typical_set)
- [T. M. Cover and J. A. Thomas, *Elements of Information Theory* (Wiley, 2nd ed., 2006)](https://doi.org/10.1002/047174882X)
