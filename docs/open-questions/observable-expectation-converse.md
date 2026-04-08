# Open: Observable Expectation Converse

**Source:** Notes, line ~1826 (JW comment: "Any ideas for a no-programming theorem?")
**Status:** Open

## Context

For spectral measurement programming, both achievability and converse are established. But for the weaker task of **expectation value programming** (just computing $\mathrm{Tr}[H\rho]$), only achievability is known.

## Question

Is there a "no-programming theorem" for observable expectation values? I.e., does the same $\frac{d^2 \delta(H)}{2}\log(1/\varepsilon)$ rate hold as a lower bound even for the weaker task?

## Difficulty

The converse for spectral measurements uses a reduction to unitary programming on the full flag manifold. Specifically, programming the projective measurement $\{P_i\}$ of $H$ is equivalent to programming the basis-change unitary $U$ that diagonalizes $H$, and the unitary programming converse gives the lower bound.

For expectation values, this reduction **breaks down** for the following reason:

1. The **spectral measurement converse** constructs a lower bound by showing that any measurement program implicitly encodes a unitary estimation scheme: if you can implement the measurement $\{P_i\}$, you can recover the unitary $U$ that diagonalizes $H$, which requires $\frac{f}{2}\log(1/\varepsilon)$ bits by the unitary programming converse.

2. For **expectation estimation**, you only need to compute the single number $\mathrm{Tr}[H\rho]$ for each input $\rho$. This does *not* require knowing the full unitary $U$ -- in principle, you could estimate $\mathrm{Tr}[H\rho]$ without being able to implement the spectral measurement at all. For instance, a randomized measurement scheme that estimates the expectation value from random projections would suffice, and such a scheme might require strictly less information about $H$ than a full spectral measurement program.

3. Therefore, the unitary estimation lower bound does not apply, and a fundamentally new argument is needed. One would need to show that even the weaker task of expectation estimation requires the same amount of quantum memory, perhaps by an information-theoretic argument about how much information about $H$ is necessarily encoded in any program that computes $\mathrm{Tr}[H\rho]$ for all $\rho$.

## Related

- [[concepts/observable-programming|Observable Programming]]
- [[concepts/unitary-programming|Unitary Programming]]
- [[concepts/free-entropy-dimension|Free Entropy Dimension]]
