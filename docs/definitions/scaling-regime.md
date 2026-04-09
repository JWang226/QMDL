# Asymptotic Scaling Regime

**Label:** `def:scaling` (Notes)
**Source:** Notes line ~650

## Statement

The **asymptotic scaling regime** for irreps $\mu, \nu$ with $\nu = \mu + \omega$ is defined by:

1. $|\mu| = \Theta(n)$ — the size of the irrep scales linearly with $n$
2. $g_\mu = \Theta(n)$ — the [[definitions/edge-gap|Edge Gap]] scales linearly with $n$
3. $\|\omega\| = O(n^s)$ for some $0 < s < 1$ — the distance between irreps is sublinear

Here $g_\mu = \min_i(\mu_i - \mu_{i+1})$ is the edge gap and $\|\omega\| = \omega_1 - \omega_d$ is the width.

## Intuition

The irreps $\mu, \nu$ are "large" (size $\sim n$) and "well-separated internally" (edge gap $\sim n$), but they differ by a "small" perturbation $\omega$ (sublinear in $n$). This is the regime where the [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] gives asymptotically perfect fidelity.

### Why this regime is natural for the compression problem

In the compression application, we need to clone from a measured Young diagram $\lambda$ to the universal target $\Lambda^*$, and back. The three conditions arise naturally:

1. **$|\mu| = \Theta(n)$:** Typical Young diagrams $\lambda$ are partitions of $n$ (the number of copies), so $|\lambda| = n$ automatically.

2. **$g_\mu = \Theta(n)$:** For a typical $\lambda$ with $\lambda_i \approx n p_i$, the edge gap is $g_\lambda \approx n \cdot \min_i(p_i - p_{i+1})$. When the eigenvalues are non-degenerate, $\min_i(p_i - p_{i+1}) > 0$ is a fixed positive constant, so $g_\lambda = \Theta(n)$. This large internal separation is what makes the [[definitions/kostka-number|Kostka Number]] monotonicity and the [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]] work: the "steps" in the Young diagram are tall enough that small perturbations cannot change the combinatorial structure of the weight multiplicities.

3. **$\|\omega\| = O(n^s)$ with $s < 1$:** The target $\Lambda^*$ is constructed by padding: $\Lambda^*_i = \lceil n x_i + (r-i)\xi_n \rceil$ with $\xi_n = O(\sqrt{n}\log n)$. For a typical $\lambda \in \mathcal{T}_{p,n}$, each $|\Lambda^*_i - \lambda_i| = O(\sqrt{n} \log n)$, so the total $L^1$ distance is $d(\Lambda^*, \lambda) = O(\sqrt{n}\log n)$, which is sublinear in $n$. This means the perturbation $\omega = \Lambda^* - \lambda$ is "small" relative to the irrep size, ensuring the cloning fidelity approaches 1.

The key interplay: the distance $\|\omega\| \sim \sqrt{n}\log n$ must be $\ll g_\mu \sim n$ for the perturbation arguments to work. Since $\sqrt{n}\log n = o(n)$, this is satisfied, and the fidelity bound $1 - O(d(\mu,\nu)/n^{1-\varepsilon})$ gives a vanishing error.

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]]
- [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]]

## External References

- [Big O notation (Wikipedia)](https://en.wikipedia.org/wiki/Big_O_notation)
- [Asymptotic analysis (Wikipedia)](https://en.wikipedia.org/wiki/Asymptotic_analysis)
