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

When $\omega = (\nu - \mu)^+$ is the [[concepts/prv-component|PRV Component]], and in the common case where $\nu - \mu$ is already dominant (meaning $\nu_i - \mu_i \geq \nu_{i+1} - \mu_{i+1}$ for all $i$), we have $d(\mu, \nu) = |\omega| = \sum_i (\nu_i - \mu_i)$. More generally, $d(\mu, \nu) = \sum_i |\nu_i - \mu_i|$, which may differ from $|\omega| = \sum_i \omega_i$ when rearrangement is needed.

## Worked Example

**Example 1:** $\mu = (5, 3, 1)$ and $\nu = (6, 2, 1)$ (both partitions of 9):

$$d(\mu, \nu) = |5 - 6| + |3 - 2| + |1 - 1| = 1 + 1 + 0 = 2$$

Geometrically: one box moves from row 2 of $\mu$ to row 1 of $\nu$. The total reshuffling is 2 (one box removed from row 2, one box added to row 1).

**Example 2:** $\mu = (7000, 3000)$ and $\Lambda^* = (8305, 3000)$ (typical vs. target in the qubit compression with $n = 10000$):

$$d(\mu, \Lambda^*) = |7000 - 8305| + |3000 - 3000| = 1305$$

This is the distance that enters the cloning fidelity bound: $F \geq 1 - O(1305/n^{1-\varepsilon})$. Since $1305 = O(\sqrt{n}\log n)$ and $n = 10000$, we get $F \geq 1 - O(n^{-1/2+\varepsilon})$, ensuring the error vanishes.

**Example 3:** $\mu = (4, 2, 0)$ and $\nu = (5, 3, 1)$ in $d = 3$:

$$d(\mu, \nu) = |4-5| + |2-3| + |0-1| = 1 + 1 + 1 = 3$$

Here $\nu - \mu = (1, 1, 1)$, which is dominant, so $\omega = (1, 1, 1)$ and $|\omega| = 3 = d(\mu, \nu)$. This corresponds to adding one box per row -- a "scalar shift" that is the simplest possible perturbation.

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- error bound is $O(d(\mu,\nu)/n^{1-\varepsilon})$
- [[results/remaining-lemmas|Dimension Ratio (Lemma 10)]]

## External References

- [W. Fulton and J. Harris, *Representation Theory: A First Course* (Springer, 1991)](https://doi.org/10.1007/978-1-4612-0979-9)
