# Asymptotic Scaling Regime

**Label:** `def:scaling` (Notes)
**Source:** Notes line ~650

## Current Article Versus Historical Notes

The numbered definition below belongs to the **Notes**. Current Article Theorem 2 is a finite inequality with $D=\|\nu-\mu\|_1$ and the supported gap $b_\mu$:

$$\text{forward error},\ \text{reverse error}\le C_{d,x}D/(b_\mu+1).$$

Thus $b_\mu=\Omega(n)$ and $D=o(n)$ suffice for vanishing error. For the actual typical-to-padded-target family, $D=O(\sqrt n\log n)$, giving $O(\log n/\sqrt n)$ trace error. These estimates are proved for the constructed rows in `TypicalRows`; see [[proof-structure]]. The Notes' width convention below is distinct from $D$, and a minimum over all ambient rows must not be substituted for the supported gap when zero rows repeat.

## Historical Notes Statement

The **asymptotic scaling regime** for irreps $\mu, \nu$ with $\nu = \mu + \omega$ is defined by:

1. $|\mu| = \Theta(n)$ — the size of the irrep scales linearly with $n$
2. $g_\mu = \Theta(n)$ — the [[definitions/edge-gap|Edge Gap]] scales linearly with $n$
3. $\|\omega\| = O(n^s)$ for some $0 < s < 1$ — the distance between irreps is sublinear

Here $g_\mu = \min_i(\mu_i - \mu_{i+1})$ is the edge gap and $\|\omega\| = \omega_1 - \omega_d$ is the width.

## Intuition

The irreps $\mu, \nu$ are "large" (size $\sim n$) and "well-separated internally" (edge gap $\sim n$), but they differ by a "small" perturbation $\omega$ (sublinear in $n$). This is the regime where the [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2; earlier Notes Theorem 1)]] gives vanishing trace-distance error.

### Comparison with the current compression application

In the compression application, we need to clone from a measured Young diagram $\lambda$ to the universal target $\Lambda^*$, and back. The three conditions arise naturally:

1. **$|\mu| = \Theta(n)$:** Typical Young diagrams $\lambda$ are partitions of $n$ (the number of copies), so $|\lambda| = n$ automatically.

2. **$b_\mu=\Theta(n)$:** For typical $\lambda$, the supported gap is bounded below by a positive multiple of $n$. The minimum runs over $1\le i\le\min(r,d-1)$, so it includes $x_r-0$ when $r<d$, but excludes pairs of zero eigenvalues. The internal supported gap controls shallow multiplicity equality and the localized Casimir estimate.

3. **$D=\|\omega\|_1=O(\sqrt n\log n)$:** The target $\Lambda^*$ is constructed by padding: $\Lambda^*_i = \lceil n x_i + (r-i+1)\xi_n \rceil$ with $\xi_n = O(\sqrt{n}\log n)$. For a typical $\lambda \in \mathcal{T}_{x,n}$, each $|\Lambda^*_i - \lambda_i| = O(\sqrt{n} \log n)$, so the total $L^1$ distance is $D=\|\Lambda^*-\lambda\|_1 = O(\sqrt{n}\log n)$, which is sublinear in $n$. The ratio $D/(b_\lambda+1)$ therefore tends to zero, giving vanishing trace-distance error in both directions.

The key comparison is $D=O(\sqrt n\log n)$ against $b_\mu=\Omega(n)$ for the perturbation arguments to work. Since $\sqrt{n}\log n = o(n)$, this is satisfied, and the direct trace-distance bound gives vanishing error.

## Used By

- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2; earlier Notes Theorem 1)]]
- [[results/lemmas/perturbation-lemma|Highest-Weight Subspace Perturbation]]

## External References

- [Big O notation (Wikipedia)](https://en.wikipedia.org/wiki/Big_O_notation)
- [Asymptotic analysis (Wikipedia)](https://en.wikipedia.org/wiki/Asymptotic_analysis)
