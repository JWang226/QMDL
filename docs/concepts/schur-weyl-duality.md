# Schur-Weyl Duality and the Schur Transform

**Appears in:** [[Letter]], [[Article]] (Sec. 2-3)

## Intuition

When you have $n$ copies of a $d$-dimensional quantum system, the total Hilbert space $(\mathbb{C}^d)^{\otimes n}$ carries two natural group actions:
- $\mathrm{GL}(d, \mathbb{C})$ acts on each copy (the "physics" symmetry -- rotating the state)
- $S_n$ permutes the copies (the "statistics" symmetry -- reordering identical particles)

Schur-Weyl duality says these two actions **perfectly complement** each other: the space decomposes into blocks labeled by Young diagrams $\lambda$ where GL acts irreducibly on one factor and $S_n$ acts irreducibly on the other.

## Formal Statement

$$(\mathbb{C}^d)^{\otimes n} \cong \bigoplus_{\lambda \vdash n, \ell(\lambda) \leq d} H_\lambda \otimes M_\lambda$$

where:
- $\lambda$ ranges over partitions of $n$ with at most $d$ parts (rows)
- $H_\lambda$ is the $\mathrm{GL}(d)$ irrep with highest weight $\lambda$
- $M_\lambda$ is the $S_n$ irrep indexed by $\lambda$
- $\dim H_\lambda$ is given by the [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]
- $\dim M_\lambda$ is given by the hook-length formula

## The Schur Transform

The **Schur transform** $V_{\mathrm{Schur}}$ is the unitary implementing this decomposition:

$$V_{\mathrm{Schur}}: (\mathbb{C}^d)^{\otimes n} \xrightarrow{\sim} \bigoplus_{\lambda \vdash n, \ell(\lambda) \leq d} H_\lambda \otimes M_\lambda$$

It simultaneously block-diagonalizes the actions of $\mathrm{GL}(d)$ and $S_n$.

### Computational Complexity

**Bacon, Chuang, and Harrow (2006)** gave an efficient quantum circuit using $O(n \cdot \mathrm{poly}(\log d, \log n))$ gates. The key idea: decompose the transform into sequential Clebsch-Gordan transforms, coupling one new tensor factor at a time.

### Spectrum Estimation Interpretation

Measuring $\lambda$ after the Schur transform is a **spectrum estimation** step. Since $\rho^{\otimes n}$ concentrates on Young diagrams with $\lambda_i/n \approx p_i$, measuring $\lambda$ gives an estimate of the spectrum with accuracy $O(1/\sqrt{n})$. This measurement is non-demolition: the post-measurement state retains all quantum information in $H_\lambda$.

## Concrete Example: Qubits ($d = 2$)

Partitions of $n$ with at most 2 parts are $\lambda = (n/2 + J, n/2 - J)$ for $J = j_{\min}, \ldots, n/2$. The decomposition becomes:

$$(\mathbb{C}^2)^{\otimes n} = \bigoplus_{J = j_{\min}}^{n/2} H_J \otimes M_J$$

This is exactly **addition of angular momenta**! Each $H_J$ is the spin-$J$ representation of SU(2) with dimension $2J + 1$.

For $n = 2$ qubits: $J = 1$ (triplet, $3 \times 1$) $\oplus$ $J = 0$ (singlet, $1 \times 1$) $= 4 = 2^2$.

## Concrete Example: Qutrits ($d = 3$)

For $n = 3$ qutrits:

| Partition $\lambda$ | Shape | $\dim H_\lambda$ | $\dim M_\lambda$ | Product |
|---|---|---|---|---|
| $(3, 0, 0)$ | One row | 10 | 1 | 10 |
| $(2, 1, 0)$ | Hook | 8 | 2 | 16 |
| $(1, 1, 1)$ | One column | 1 | 1 | 1 |

Total: $10 + 16 + 1 = 27 = 3^3$.

## What Happens to $\rho^{\otimes n}$

Under the Schur transform:

$$\rho^{\otimes n} = \bigoplus_\lambda q_\lambda \cdot \rho_\lambda \otimes \frac{I_{M_\lambda}}{\dim M_\lambda}$$

where:
- $q_\lambda = s_\lambda(p)$ is the [[concepts/schur-polynomials|Schur Polynomial]] evaluated at the eigenvalues -- the **probability** of sector $\lambda$
- $\rho_\lambda = \pi_\lambda(\rho) / s_\lambda(p)$ is the normalized GL irrep state -- contains all **eigenbasis information**
- The $S_n$ part is **maximally mixed** -- carries no information about $\rho$'s eigenbasis

The GL part $\rho_\lambda$ is block-diagonal in the weight basis:

$$\rho_\lambda = \sum_{\delta \in Q_+} p_\lambda(\delta) \Pi_{\lambda - \delta}$$

where $p_\lambda(\delta) = x^{\lambda - \delta}/s_\lambda(x)$ are the eigenvalues and weight multiplicities $m_\lambda(\delta) = K_{\lambda, \lambda - \delta}$ are [[definitions/kostka-number|Kostka numbers]].

## Role in the Project

The Schur transform is **Step 1** of both encoding and decoding:

1. **Compression**: only need to store $\rho_\lambda$ (the $S_n$ part is reconstructable)
2. **Sector selection**: Young diagrams $\lambda$ concentrate near $\lambda \approx np$ (by Sanov's theorem)
3. **Memory cost**: $\log|M_n| \approx \log \dim H_{\Lambda^*}$, giving $O(\log n)$ scaling
4. **Cloning between sectors**: the [[concepts/generalized-cloning-map|Generalized Cloning Map]] maps $\rho_\lambda$ to $\rho_{\Lambda^*}$

## Related

- [[concepts/schur-polynomials|Schur Polynomials]] -- probability of each sector
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] -- dimension of $H_\lambda$
- [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin Basis]] -- explicit basis for $H_\lambda$
- [[concepts/young-diagrams|Young Diagrams]] -- the labels $\lambda$
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- the compression task
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- maps between sectors
- [[results/achievability|Achievability (State Compression)]] -- uses the Schur transform as Step 1

## External References

- [Schur-Weyl duality (Wikipedia)](https://en.wikipedia.org/wiki/Schur%E2%80%93Weyl_duality)
- R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer (2009)
- [W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer (1991)](https://doi.org/10.1007/978-1-4612-0979-9)
- A. W. Harrow, "Applications of coherent classical communication and the Schur transform to quantum information theory," PhD thesis, MIT (2005)
