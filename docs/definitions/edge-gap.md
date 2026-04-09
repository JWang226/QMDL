# Edge Gap

**Source:** Article, Notes (used throughout)

## Statement

For a partition / highest weight $\lambda = (\lambda_1, \lambda_2, \ldots, \lambda_d)$, the **edge gap** is:

$$g_\lambda = \min_{1 \leq i \leq d-1} (\lambda_i - \lambda_{i+1})$$

## Intuition

The edge gap measures the smallest "step" in the Young diagram. A large edge gap means the partition is "well-separated" -- no two rows have nearly the same length. For typical partitions $\lambda \approx np$, the edge gap is $g_\lambda \approx n \cdot \min_i(p_i - p_{i+1})$, which is $\Theta(n)$ when the eigenvalues are non-degenerate.

## Role in the Project

The edge gap controls when the [[results/lemmas/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] gives **equality**: $K_{\mu, \mu-\delta} = K_{\mu+\omega, \mu+\omega-\delta}$ whenever $|\delta| \leq g_\mu$. This equality is essential for the [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]].

### What happens when $g_\lambda = 0$

When $g_\lambda = 0$, the partition has a "flat spot": two adjacent rows have the same length ($\lambda_i = \lambda_{i+1}$ for some $i$). This causes several problems:

1. **Weight multiplicity instability:** The Kostka number monotonicity $K_{\mu, \mu-\delta} = K_{\mu+\omega, \mu+\omega-\delta}$ breaks down when $|\delta|$ exceeds the edge gap. With $g_\lambda = 0$, even an infinitesimal perturbation $\omega$ can change the weight multiplicities, because adding boxes to equal-length rows creates ambiguity in the combinatorial structure.

2. **The perturbation lemma fails:** The [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]] relies on the weight spaces of $H_\mu$ and $H_{\mu+\omega}$ being "aligned" for low weights ($|\delta| \leq g_\mu$). When $g_\mu = 0$, there is no safe range of weights where alignment is guaranteed.

3. **Degenerate eigenvalues in $\rho$:** A flat spot $\lambda_i = \lambda_{i+1}$ in a typical Young diagram $\lambda \approx np$ implies $p_i \approx p_{i+1}$, meaning eigenvalues of $\rho$ are nearly degenerate. The unitary orbit of $\rho$ shrinks near degeneracies, and the free entropy dimension drops. This is the representation-theoretic manifestation of eigenvalue collision.

This is why the main theorems assume **non-degenerate eigenvalues**: it guarantees $g_\lambda = \Theta(n)$ for typical $\lambda$, placing us squarely in the [[definitions/scaling-regime|Scaling Regime]].

## Qubit Example ($d = 2$)

For a qubit partition $\lambda = (\lambda_1, \lambda_2)$ with $\lambda_1 + \lambda_2 = n$:

$$g_\lambda = \lambda_1 - \lambda_2$$

- If $\rho$ has eigenvalues $p = 0.7$ and $1-p = 0.3$, a typical partition has $\lambda_1 \approx 0.7n$ and $\lambda_2 \approx 0.3n$, giving $g_\lambda \approx 0.4n$. For $n = 1000$: $g_\lambda \approx 400$.
- The partition $(500, 500)$ has $g_\lambda = 0$ -- this corresponds to the "spin-0" sector ($J = 0$), which occurs when $\lambda_1 = \lambda_2 = n/2$. This only arises as a typical partition when $p = 1/2$ (maximally mixed state), where the orbit is trivial and compression is trivial.

## Used By

- [[definitions/scaling-regime|Scaling Regime]]
- [[results/lemmas/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]]
- [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]]
- [[results/lemmas/probability-ratio|Probability Ratio (Lemma 9)]]

## External References

- [Weyl character formula (Wikipedia)](https://en.wikipedia.org/wiki/Weyl_character_formula)
