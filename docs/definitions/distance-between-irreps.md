# Distance Between Irreps

**Source:** Article (used throughout)

## Statement

For partitions $\mu = (\mu_1, \ldots, \mu_d)$ and $\nu = (\nu_1, \ldots, \nu_d)$:

$$d(\mu, \nu) = \sum_{i=1}^d |\mu_i - \nu_i|$$

This is simply the $L^1$ distance between the partitions viewed as integer vectors.

## Geometric Meaning

The $L^1$ distance $d(\mu, \nu) = \sum_i |\mu_i - \nu_i|$ measures the **total number of boxes that must be reshuffled** to transform one Young diagram into the other. Visualizing $\mu$ and $\nu$ as Young diagrams (rows of boxes, left-justified), $d(\mu, \nu)$ counts the total number of boxes that are in $\mu$ but not $\nu$, plus the number in $\nu$ but not $\mu$ -- i.e., the symmetric difference measured row-by-row.

Since $|\mu| = \sum_i \mu_i$ and $|\nu| = \sum_i \nu_i$ need not be equal (they can be partitions of different integers), $d(\mu, \nu)$ also accounts for "adding" or "removing" boxes. When $|\mu| = |\nu|$, $d(\mu, \nu)$ is exactly twice the number of boxes that need to be moved from one row to another.

## Relation to PRV Component

Dominance of $\omega=\nu-\mu$ means that its entries are weakly decreasing; they may be negative. The current Article Theorem 2 uses

$$D=\|\omega\|_1=\sum_i|\nu_i-\mu_i|.$$

Only when every increment is nonnegative does $D=\sum_i(\nu_i-\mu_i)$. Rearranging a vector preserves both its sum and its $L^1$ norm, so rearrangement itself is not the source of a difference between them. For example, $\mu=(3,2)$, $\nu=(4,1)$ gives the dominant signed difference $(1,-1)$: $D=2$ but its ordinary sum is zero.

`differenceNorm` in `CanonicalRowBounds.lean` computes this exact integer distance. The formal theorem includes signed dominant differences; it does not add an entrywise nonnegativity hypothesis.

## Worked Example

**Example 1:** $\mu = (5, 3, 1)$ and $\nu = (6, 2, 1)$ (both partitions of 9):

$$d(\mu, \nu) = |5 - 6| + |3 - 2| + |1 - 1| = 1 + 1 + 0 = 2$$

Geometrically: one box moves from row 2 of $\mu$ to row 1 of $\nu$. The total reshuffling is 2 (one box removed from row 2, one box added to row 1).

**Example 2:** $\mu = (7000, 3000)$ and $\Lambda^* = (8305, 3000)$ (a possible pair of qubit rows):

$$d(\mu, \Lambda^*) = |7000 - 8305| + |3000 - 3000| = 1305$$

This is an illustrative row distance, not the current padded target from the Article. In Theorem 2, the error is bounded by $C_{d,x}D/(b_\mu+1)$. For the actual typical-to-target family, $D=O(\sqrt n\log n)$ and $b_\mu=\Omega(n)$.

**Example 3:** $\mu = (4, 2, 0)$ and $\nu = (5, 3, 1)$ in $d = 3$:

$$d(\mu, \nu) = |4-5| + |2-3| + |0-1| = 1 + 1 + 1 = 3$$

Here $\nu - \mu = (1, 1, 1)$, which is dominant, so $\omega = (1, 1, 1)$ and $|\omega| = 3 = d(\mu, \nu)$. This corresponds to adding one box per row -- a "scalar shift" that is the simplest possible perturbation.

## Used By

- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]] -- error bound is $C_{d,x}D/(b_\mu+1)$
- [[results/lemmas/dimension-ratio|Dimension Ratio]]

## External References

- [W. Fulton and J. Harris, *Representation Theory: A First Course* (Springer, 1991)](https://doi.org/10.1007/978-1-4612-0979-9)
