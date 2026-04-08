# Kostka Number

**Source:** Article, Notes (used throughout)

## Statement

The **Kostka number** $K_{\lambda, w}$ is the multiplicity of the weight $w$ in the $\mathrm{GL}(d)$ irreducible representation $H_\lambda$:

$$K_{\lambda, w} = \dim (H_\lambda)_w$$

Equivalently, $K_{\lambda, w}$ counts the number of [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin patterns]] with top row $\lambda$ and weight $w$.

In terms of [[concepts/schur-polynomials|Schur Polynomials]]:

$$s_\lambda(x) = \sum_w K_{\lambda, w} \cdot x^w$$

## Intuition

Kostka numbers count "how many ways" a given weight can arise inside a representation. Equivalently, $K_{\lambda, w}$ counts the number of **semistandard Young tableaux** (SSYT) of shape $\lambda$ and content $w$. An SSYT is a filling of the Young diagram $\lambda$ with positive integers such that rows are weakly increasing left-to-right and columns are strictly increasing top-to-bottom, and the content records how many times each integer $i$ appears (giving weight $w_i$).

For the highest weight ($\delta = 0$), $K_{\lambda, \lambda} = 1$ -- there is exactly one SSYT of shape $\lambda$ and content $\lambda$ (fill row $i$ entirely with the integer $i$). As $|\delta|$ increases, the multiplicities grow polynomially (bounded by Kostant's partition function).

## Worked Examples

### Example 1: $K_{(2,1), (2,1)} = 1$

Shape $\lambda = (2,1)$ (two boxes in the first row, one in the second), content $w = (2,1)$ (two 1's and one 2). The unique SSYT is:

$$\begin{array}{|c|c|}\hline 1 & 1 \\\hline 2 \\\cline{1-1}\end{array}$$

(Rows weakly increasing, columns strictly increasing.)

### Example 2: $K_{(2,1), (1,1,1)} = 1$

Shape $\lambda = (2,1)$, content $w = (1,1,1)$ (one each of 1, 2, 3). The unique SSYT is:

$$\begin{array}{|c|c|}\hline 1 & 2 \\\hline 3 \\\cline{1-1}\end{array}$$

Wait -- we must check: columns strictly increasing requires $1 < 3$, which holds. But we also need $1 < 2$ in the first row (weakly), which holds. However, we could also try:

$$\begin{array}{|c|c|}\hline 1 & 3 \\\hline 2 \\\cline{1-1}\end{array}$$

Column condition: $1 < 2$ holds. Row condition: $1 \leq 3$ holds. This is also valid. So $K_{(2,1), (1,1,1)} = 2$.

### Example 3: $K_{(3), (1,1,1)} = 1$

Shape $\lambda = (3)$ (one row of three), content $w = (1,1,1)$. The only filling is:

$$\begin{array}{|c|c|c|}\hline 1 & 2 & 3 \\\hline\end{array}$$

So $K_{(3), (1,1,1)} = 1$.

### Example 4: $K_{(1,1,1), (1,1,1)} = 1$

Shape $\lambda = (1,1,1)$ (one column of three), content $w = (1,1,1)$. The only filling is:

$$\begin{array}{|c|}\hline 1 \\\hline 2 \\\hline 3 \\\hline\end{array}$$

So $K_{(1,1,1), (1,1,1)} = 1$.

### Example 5: Qubit ($d = 2$)

For $d = 2$, all partitions have at most 2 rows: $\lambda = (\lambda_1, \lambda_2)$. The weights are $w = (\lambda_1 - k, \lambda_2 + k)$ for $k = 0, \ldots, \lambda_1 - \lambda_2$. For each such $w$, $K_{\lambda, w} = 1$: there is exactly one SSYT with the given content. This is because with only two symbols, the column-strict and row-weak conditions fully determine the tableau. This is why $\rho_\lambda$ is fully diagonal (not just block-diagonal) for qubits.

## Connection to the Schur Polynomial

The Schur polynomial expands as a sum over weights, with Kostka numbers as coefficients:

$$s_\lambda(x) = \sum_w K_{\lambda, w} \cdot x^w$$

This is the "combinatorial definition" of Schur polynomials. The normalization of $\rho_\lambda$ is $\mathrm{Tr}[\pi_\lambda(\rho)] = s_\lambda(x)$, and the dimension of the weight-$w$ block is $K_{\lambda, w}$.

## Used By

- [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]]
- [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]]
- [[results/tail-mass|Tail Mass (Lemma 8)]]
- [[results/probability-ratio|Probability Ratio (Lemma 9)]]
- [[definitions/normalized-gl-irrep|Normalized GL Irrep State]]

## External References

- [Kostka number (Wikipedia)](https://en.wikipedia.org/wiki/Kostka_number)
- [Stanley, *Enumerative Combinatorics*, Vol. 2 (Cambridge University Press, 1999)](https://doi.org/10.1017/CBO9780511609589)
- [Macdonald, *Symmetric Functions and Hall Polynomials* (Oxford University Press, 2nd ed., 1995)](https://doi.org/10.1017/S0013091500023592)
