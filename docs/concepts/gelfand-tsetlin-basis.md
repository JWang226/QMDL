# Gelfand-Tsetlin (GT) Basis

**Appears in:** [[Article]] (Sec. 6.1), [[Notes]] (Sec. 4.1)

## Intuition

The Gelfand-Tsetlin basis provides an explicit, canonical basis for any irreducible representation of $\mathrm{GL}(d, \mathbb{C})$. It works by restricting the representation down the chain $\mathrm{GL}(d) \supset \mathrm{GL}(d-1) \supset \cdots \supset \mathrm{GL}(1)$. At each step, the irrep breaks into smaller irreps, and the sequence of labels at each level gives a **GT pattern** -- a triangular array of integers that uniquely identifies each basis vector.

## Formal Description

A GT pattern for the irrep $H_\lambda$ (with $\lambda = (\lambda_1, \ldots, \lambda_d)$) is a triangular array:

$$\begin{pmatrix} \lambda_1^{(d)} & & \lambda_2^{(d)} & & \cdots & & \lambda_d^{(d)} \\ & \lambda_1^{(d-1)} & & \lambda_2^{(d-1)} & & \cdots & \lambda_{d-1}^{(d-1)} \\ & & & \ddots & & & \\ & & & & \lambda_1^{(1)} & & \end{pmatrix}$$

where:
- Top row: $\lambda^{(d)} = \lambda$ (the highest weight)
- **Interlacing conditions**: $\lambda_i^{(k)} \geq \lambda_i^{(k-1)} \geq \lambda_{i+1}^{(k)}$ for all valid $i, k$

The **weight** of a GT pattern is $w_i = \sum_j \lambda_j^{(i)} - \sum_j \lambda_j^{(i-1)}$.

## Concrete Example: $\mathrm{GL}(3)$, Irrep $\lambda = (3, 1, 0)$

Consider the irrep $H_{(3,1,0)}$ of $\mathrm{GL}(3)$. A GT pattern has the form:

$$\begin{pmatrix} 3 & & 1 & & 0 \\ & a & & b & \\ & & c & & \end{pmatrix}$$

with interlacing conditions: $3 \geq a \geq 1$, $1 \geq b \geq 0$, and $a \geq c \geq b$. One specific GT pattern is:

$$\begin{pmatrix} 3 & & 1 & & 0 \\ & 2 & & 1 & \\ & & 1 & & \end{pmatrix}$$

**Reading off the weight:** The weight $w = (w_1, w_2, w_3)$ is computed from the row sums:

- Row 3 sum: $3 + 1 + 0 = 4$
- Row 2 sum: $2 + 1 = 3$
- Row 1 sum: $1$

Then $w_3 = 4 - 3 = 1$, $w_2 = 3 - 1 = 2$, $w_1 = 1$. So this basis vector has weight $(1, 2, 1)$.

The total number of valid GT patterns for $H_{(3,1,0)}$ equals $\dim H_{(3,1,0)} = 8$ (by the [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]).

## Role in the Project

The GT basis is crucial for the [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] proof:

1. **Weight space decomposition**: The irrep $H_\mu$ decomposes into weight spaces, each spanned by GT patterns with the same weight
2. **Kostka numbers**: $K_{\mu, w}$ = number of GT patterns with weight $w$ = dimension of weight space
3. **Perturbation analysis**: The [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]] compares GT bases of $H_\mu$ and $H_\nu$ when $\nu \approx \mu$
4. **Injection map**: An injection $\phi_\omega$ from GT patterns of $H_\mu$ to GT patterns of $H_{\mu + \omega}$ is used to prove [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]]

## Related

- [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] -- uses GT pattern injection
- [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]] -- perturbs GT basis
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- the decomposition where these bases live

## External References

- [Gelfand-Tsetlin basis (Wikipedia)](https://en.wikipedia.org/wiki/Gelfand%E2%80%93Tsetlin_basis)
- I. M. Gelfand and M. L. Tsetlin, "Finite-dimensional representations of the group of unimodular matrices," *Doklady Akad. Nauk SSSR* 71, 825--828 (1950)
- [Molev, "Gelfand-Tsetlin bases for classical Lie algebras" (2006)](https://arxiv.org/abs/math/0211289)
- A. I. Molev, *Yangians and Classical Lie Algebras*, AMS Mathematical Surveys and Monographs (2007)
