# Schur-Weyl Duality

**Appears in:** [[Letter]], [[Article]] (Sec. 2-3)

## Intuition

When you have $n$ copies of a $d$-dimensional quantum system, the total Hilbert space $(\mathbb{C}^d)^{\otimes n}$ carries two natural group actions:
- $\mathrm{GL}(d, \mathbb{C})$ acts on each copy (the "physics" symmetry -- rotating the state)
- $S_n$ permutes the copies (the "statistics" symmetry -- reordering identical particles)

Schur-Weyl duality says these two actions **perfectly complement** each other: the space decomposes into blocks labeled by Young diagrams $\lambda$ where GL acts irreducibly on one factor and $S_n$ acts irreducibly on the other. No information is shared between the two factors -- they are in a precise sense "dual."

## Formal Statement

$$(\mathbb{C}^d)^{\otimes n} \cong \bigoplus_{\lambda \vdash n, \ell(\lambda) \leq d} H_\lambda \otimes M_\lambda$$

where:
- $\lambda$ ranges over partitions of $n$ with at most $d$ parts (rows)
- $H_\lambda$ is the $\mathrm{GL}(d)$ irrep with highest weight $\lambda$
- $M_\lambda$ is the $S_n$ irrep indexed by $\lambda$
- $\dim H_\lambda$ is given by the [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]
- $\dim M_\lambda$ is given by the hook-length formula

The **Schur transform** $V_{\mathrm{Schur}}$ is the unitary implementing this decomposition.

## Concrete Example: Qubits ($d = 2$)

For $n$ qubits, partitions of $n$ with at most 2 parts are $\lambda = (n/2 + J, n/2 - J)$ for $J = j_{\min}, \ldots, n/2$, where $j_{\min} = 0$ or $1/2$ depending on parity. The decomposition becomes:

$$(\mathbb{C}^2)^{\otimes n} = \bigoplus_{J = j_{\min}}^{n/2} H_J \otimes M_J$$

This is exactly the **addition of angular momenta** from quantum mechanics! Each $H_J$ is the spin-$J$ representation of SU(2) with dimension $2J + 1$, and $M_J$ is the multiplicity space counting the number of ways $n$ spin-1/2 particles can couple to total spin $J$.

For example, with $n = 2$ qubits:
- $J = 1$: the triplet $H_1 \cong \mathbb{C}^3$ (symmetric subspace $\mathrm{Sym}^2(\mathbb{C}^2)$), with $M_1 \cong \mathbb{C}^1$
- $J = 0$: the singlet $H_0 \cong \mathbb{C}^1$ (antisymmetric subspace), with $M_0 \cong \mathbb{C}^1$

Total: $3 \times 1 + 1 \times 1 = 4 = 2^2$, as expected.

## Concrete Example: Qutrits ($d = 3$)

For $d = 3$, partitions of $n$ with at most 3 parts are parameterized by **two-dimensional** Young diagrams. For instance, with $n = 3$ qutrits, the partitions of 3 with $\leq 3$ parts are:

| Partition $\lambda$ | Young diagram shape | $\dim H_\lambda$ | $\dim M_\lambda$ | Product |
|---|---|---|---|---|
| $(3, 0, 0)$ | One row of 3 | 10 | 1 | 10 |
| $(2, 1, 0)$ | Hook shape | 8 | 2 | 16 |
| $(1, 1, 1)$ | One column of 3 | 1 | 1 | 1 |

Total: $10 + 16 + 1 = 27 = 3^3$, confirming the decomposition.

The key difference from qubits: with $d \geq 3$, the partitions are genuinely two-dimensional (not just parameterized by a single number $J$), so the structure of typical sectors is richer.

## What Happens to $\rho^{\otimes n}$

Under the Schur transform, the i.i.d. state decomposes as:

$$\rho^{\otimes n} = \bigoplus_\lambda q_\lambda \cdot \rho_\lambda \otimes \frac{I_{M_\lambda}}{\dim M_\lambda}$$

where:
- $q_\lambda = s_\lambda(p)$ is the [[concepts/schur-polynomials|Schur Polynomial]] evaluated at the eigenvalues $p = (p_1, \ldots, p_d)$ of $\rho$ -- this gives the **probability** of measuring sector $\lambda$
- $\rho_\lambda = \pi_\lambda(\rho) / s_\lambda(p)$ is the normalized GL irrep state -- this contains all the **eigenbasis information** about $\rho$
- The $S_n$ part is **maximally mixed** -- the $S_n$ irrep carries **no information** about $\rho$'s eigenbasis, only about the statistics of which copies were permuted

The crucial point is the factored structure: the GL part $\rho_\lambda$ encodes what we need to recover (the eigenbasis), while the $S_n$ part $I/\dim M_\lambda$ is completely determined by the sector label $\lambda$ and can be freely discarded and recreated. This is why compression to $O(\log n)$ qubits is possible.

### How the Schur transform acts on the GL part

The state $\rho_\lambda$ is block-diagonal in the weight basis:

$$\rho_\lambda = \sum_{\delta \in Q_+} p_\lambda(\delta) \Pi_{\lambda - \delta}$$

where $p_\lambda(\delta) = x^{\lambda - \delta}/s_\lambda(x)$ are the eigenvalues (monomial ratios weighted by the Schur polynomial) and $\Pi_{\lambda - \delta}$ projects onto the weight space of weight $\lambda - \delta$. The highest weight has the largest eigenvalue, and the weight multiplicities $m_\lambda(\delta) = K_{\lambda, \lambda - \delta}$ are given by Kostka numbers.

## Role in the Project

This decomposition is the starting point for everything:

1. **Compression**: only need to store the GL part $\rho_\lambda$ (the $S_n$ part is fixed and reconstructable)
2. **Sector selection**: Young diagrams $\lambda$ concentrate near $\lambda \approx np$ (by Sanov's theorem), with fluctuations of order $\sqrt{n}$
3. **Memory cost**: $\log|M_n| \approx \log \dim H_{\Lambda^*}$ for the target irrep, giving the $O(\log n)$ scaling via the [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]
4. **Cloning between sectors**: the [[concepts/generalized-cloning-map|Generalized Cloning Map]] maps $\rho_\lambda$ to $\rho_{\Lambda^*}$ with high fidelity for all typical $\lambda$

## Related

- [[concepts/schur-polynomials|Schur Polynomials]] -- normalization/probability of each sector
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] -- dimension of $H_\lambda$
- [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin Basis]] -- explicit basis for $H_\lambda$
- [[concepts/young-diagrams|Young Diagrams]] -- the labels $\lambda$
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- the compression task
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- maps between different sectors

## External References

- [Schur-Weyl duality (Wikipedia)](https://en.wikipedia.org/wiki/Schur%E2%80%93Weyl_duality)
- R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Graduate Texts in Mathematics, Springer (2009)
- W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics, Springer (1991)
