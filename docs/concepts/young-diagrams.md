# Young Diagrams and Partitions

**Appears in:** All three papers

## Definition

A **partition** of $n$ into at most $d$ parts is a weakly decreasing sequence $\lambda = (\lambda_1 \geq \lambda_2 \geq \cdots \geq \lambda_d \geq 0)$ with $|\lambda| = \sum_i \lambda_i = n$. A **Young diagram** is the graphical representation: $\lambda_i$ boxes in row $i$.

### Example: $\lambda = (4, 2, 1)$, a partition of 7

```
+--+--+--+--+
|  |  |  |  |     <- row 1: 4 boxes
+--+--+--+--+
|  |  |
+--+--+           <- row 2: 2 boxes
|  |
+--+               <- row 3: 1 box
```

Here $|\lambda| = 7$, $\ell(\lambda) = 3$, the width is $4-1=3$, and the minimum adjacent-row gap is $\min(4-2,2-1)=1$.

## Role in Schur-Weyl Duality

Young diagrams label the irreducible components of $(\mathbb{C}^d)^{\otimes n}$:
- Each $\lambda \vdash n$ with $\ell(\lambda) \leq d$ gives a $\mathrm{GL}(d)$ irrep $H_\lambda$ and an $S_n$ irrep $M_\lambda$
- The state $\rho^{\otimes n}$ concentrates on Young diagrams with $\lambda/n \approx p$ (the eigenvalue distribution)

## Key Quantities

| Quantity | Symbol | Meaning |
|----------|--------|---------|
| Size | $\lvert\lambda\rvert = \sum_i \lambda_i$ | Total number of boxes |
| Length | $\ell(\lambda)$ | Number of nonzero rows |
| Width | $\lambda_1 - \lambda_d$ | Historical Notes writes this as $\|\lambda\|$; it is not the current $L^1$ norm |
| Full adjacent-row gap | $\min_{1\le i<d}(\lambda_i - \lambda_{i+1})$ | Vanishes when two zero rows occur; not the supported gap used in the current cloning theorem |
| GL dimension | $\dim H_\lambda$ | Given by [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] |
| $S_n$ dimension | $\dim M_\lambda$ | Given by hook-length formula (see below) |
| Schur polynomial | $s_\lambda(x)$ | Character of $H_\lambda$ |
| [[definitions/kostka-number|Kostka Number]] | $K_{\lambda, w}$ | Weight multiplicity |

The current Article Theorem 2 uses $D=\|\nu-\mu\|_1$, the sum of absolute
row differences, and $b_\mu=\min_{1\le i\le\min(r,d-1)}(\mu_i-\mu_{i+1})$.
This supported gap includes the last positive-to-zero boundary but excludes
adjacent pairs of trailing zeros. See [[definitions/edge-gap]] and [[notation]].

## The Hook-Length Formula for $\dim M_\lambda$

The dimension of the $S_n$ irrep $M_\lambda$ is given by the **Frame-Robinson-Thrall hook-length formula**:

$$\dim M_\lambda = \frac{n!}{\prod_{\square \in \lambda} h(\square)}$$

where the product is over all boxes $\square$ in the Young diagram, and $h(\square)$ is the **hook length** of box $\square$: the number of boxes directly to its right plus the number directly below it, plus 1 (for the box itself).

**Example:** For $\lambda = (3, 1)$ (a partition of 4):

```
+--+--+--+
| 4| 2| 1|     hook lengths
+--+--+--+
| 1|
+--+
```

The hooks are $h = 4, 2, 1, 1$, so $\dim M_{(3,1)} = 4!/(4 \cdot 2 \cdot 1 \cdot 1) = 3$.

This formula is important because $\dim M_\lambda$ controls the multiplicity of the GL$(d)$ irrep $H_\lambda$ in the Schur-Weyl decomposition. In the compression scheme, this register is maximally mixed and independent of the unknown eigenbasis, so it can be discarded and regenerated.

## The Typical Young Diagram

For eigenvalues $p = (p_1, \ldots, p_r, 0, \ldots, 0)$, the typical Young diagram has:
- $\lambda_i \approx n p_i$ for $i \leq r$
- $\lambda_i = 0$ for $i > r$
- Fluctuations of order $O(\sqrt{n})$

The current Article's [[definitions/typical-set|typical set]] uses the wider
$O(\sqrt n\log n)$ coordinate window to make the atypical mass vanish with
the required quantitative bound.

## Related

- [[concepts/schur-weyl-duality|Schur-Weyl Duality]]
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]
- [[definitions/edge-gap|Edge Gap]]
- [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin Basis]]

## External References

- [Young diagram (Wikipedia)](https://en.wikipedia.org/wiki/Young_diagram)
- [Young tableau (Wikipedia)](https://en.wikipedia.org/wiki/Young_tableau)
- W. Fulton, *Young Tableaux: With Applications to Representation Theory and Geometry*, London Mathematical Society Student Texts, Cambridge University Press (1997)
- R. P. Stanley, *Enumerative Combinatorics, Volume 2*, Cambridge Studies in Advanced Mathematics, Cambridge University Press (1999)
