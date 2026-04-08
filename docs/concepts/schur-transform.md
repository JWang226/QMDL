# Schur Transform

**Appears in:** All three papers

## Definition

The **Schur transform** is the unitary $V_{\mathrm{Schur}}$ that implements the [[concepts/schur-weyl-duality|Schur-Weyl Duality]] decomposition:

$$V_{\mathrm{Schur}}: (\mathbb{C}^d)^{\otimes n} \xrightarrow{\sim} \bigoplus_{\lambda \vdash n, \ell(\lambda) \leq d} H_\lambda \otimes M_\lambda$$

It simultaneously block-diagonalizes the actions of $\mathrm{GL}(d)$ (on each tensor factor) and $S_n$ (permuting tensor factors).

## What It Does to $\rho^{\otimes n}$

$$V_{\mathrm{Schur}} \rho^{\otimes n} V_{\mathrm{Schur}}^\dagger = \bigoplus_\lambda s_\lambda(p) \cdot \rho_\lambda \otimes \frac{I_{M_\lambda}}{\dim M_\lambda}$$

After the Schur transform:
1. **Measure** the label $\lambda$ (non-destructive, classical)
2. The GL part $\rho_\lambda$ contains all eigenbasis information
3. The $S_n$ part is maximally mixed (no information)

## Computational Complexity

The Schur transform can be implemented efficiently as a quantum circuit:

- **Bacon, Chuang, and Harrow (2006)** gave an efficient quantum circuit for the Schur transform using $O(n \cdot \mathrm{poly}(\log d, \log n))$ gates. The key idea is to decompose the transform into a sequence of Clebsch-Gordan transforms, each coupling one new tensor factor at a time into the running irrep label.

- **Spectrum estimation interpretation:** The measurement of $\lambda$ after the Schur transform is precisely a **spectrum estimation** step. Since $\rho^{\otimes n}$ concentrates on Young diagrams with $\lambda_i / n \approx p_i$ (the eigenvalues of $\rho$), measuring $\lambda$ gives an estimate of the spectrum $p$ with accuracy $O(1/\sqrt{n})$. This is the quantum analogue of measuring the type (empirical distribution) of an i.i.d. classical source. Remarkably, this measurement is *non-demolition*: the post-measurement state retains all quantum information in the GL$(d)$ irrep $H_\lambda$.

## Role in the Project

The Schur transform is **Step 1** of both the encoding and decoding protocols in [[results/achievability|Achievability (State Compression)]]. It reduces the compression problem from the full $d^n$-dimensional space to the $O(\text{poly}(n))$-dimensional GL irreps.

## Related

- [[concepts/schur-weyl-duality|Schur-Weyl Duality]]
- [[results/achievability|Achievability (State Compression)]]
- [[concepts/young-diagrams|Young Diagrams and Partitions]]

## External References

- [Schur-Weyl duality (Wikipedia)](https://en.wikipedia.org/wiki/Schur%E2%80%93Weyl_duality)
- [Bacon, Chuang, and Harrow, "Efficient quantum circuits for Schur and Clebsch-Gordan transforms" (2006)](https://arxiv.org/abs/quant-ph/0601001)
- A. W. Harrow, "Applications of coherent classical communication and the Schur transform to quantum information theory," PhD thesis, MIT (2005)
