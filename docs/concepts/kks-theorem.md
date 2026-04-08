# Kirillov-Kostant-Souriau (KKS) Theorem

**Appears in:** Letter, Notes

## Overview

The Kirillov-Kostant-Souriau theorem connects **symplectic geometry** (classical phase spaces) with **representation theory** (quantum Hilbert spaces) via geometric quantization. It associates to each coadjoint orbit of a Lie group a unitary irreducible representation.

## Statement (Rough)

For a compact Lie group $G$ (e.g., $U(d)$), each coadjoint orbit $\mathcal{O}_\lambda \subset \mathfrak{g}^*$ carries a natural symplectic structure. The geometric quantization of $\mathcal{O}_\lambda$ produces the irreducible representation $H_\lambda$.

Key consequence: $\dim H_\lambda \sim \mathrm{Vol}(\mathcal{O}_\lambda)^{1/2}$ (in appropriate units).

## Role in the Project

The KKS theorem explains the **factor of 1/2** between the physical free entropy and the QMDL:

$$\log|M_n| = \frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1/2}) + \text{const} + o(1)$$

### Why Exactly 1/2? The Vandermonde Squared vs. Vandermonde

The factor of 1/2 is not a mathematical accident -- it is the precise signature of geometric quantization. To understand it, trace where the [[concepts/vandermonde-determinant|Vandermonde Determinant]] $\Delta(p) = \prod_{i<j}(p_i - p_j)$ appears on each side:

**Classical side (physical free entropy):** Voiculescu's free entropy is defined using the flat Euclidean (Lebesgue) measure on $d \times d$ Hermitian matrices. When changing from matrix coordinates to eigenvalue-eigenvector coordinates, the Jacobian of the eigenvalue-eigenvector decomposition produces a **squared** Vandermonde determinant $\Delta(p)^2$. This is because each pair of eigenvalues $(p_i, p_j)$ is separated by **two real continuous dimensions** (the off-diagonal matrix entries are complex, contributing one real dimension each for the real and imaginary parts). The volume element becomes:

$$dV_{\text{Euclidean}} \propto \Delta(p)^2 \, dp_1 \cdots dp_d \, d\mu_{\text{Haar}}$$

**Quantum side (QMDL):** The QMDL is $\log \dim H_\lambda$, governed by the [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]. By the KKS theorem, the asymptotic dimension of the irrep $H_\lambda$ equals the **symplectic volume** of the corresponding coadjoint orbit $\mathcal{O}_\lambda$. The natural symplectic form on $\mathcal{O}_\lambda$ pairs the $d(d-1)$ real orbital dimensions into $d(d-1)/2$ canonically conjugate pairs (position-momentum pairs). The Liouville measure on the orbit therefore scales with only the **first power** of the Vandermonde:

$$\mathrm{Vol}_{\text{symplectic}}(\mathcal{O}_\lambda) \propto \Delta(p)$$

**The punchline:** Since $\log \Delta(p)^2 = 2 \log \Delta(p)$, taking logarithms gives:

$$\chi_{\mathrm{phy}} \sim 2 \log \Delta(p), \qquad \log|M_n| \sim \log \Delta(p)$$

The factor of 1/2 is thus the contraction ratio from continuous flat geometry (Euclidean volume with $\Delta^2$) to discrete symplectic phase space (Liouville volume with $\Delta^1$). In the language of geometric quantization: **2 real dimensions map to 1 complex dimension**.

$$\dim_{\mathbb{R}}(\text{classical phase space}) = 2 \times \dim_{\mathbb{C}}(\text{quantum Hilbert space})$$

## Connection to Kirillov Character Formula

The authors conjecture (see [[open-questions/unitary-subleading|Open: Subleading Term for Unitary Programming]]) that the $O(1)$ subleading term for unitary programming involves the **Kirillov character formula**, which gives the character of $H_\lambda$ as an integral over $\mathcal{O}_\lambda$.

## Related

- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[concepts/flag-manifold|Flag Manifold]]
- [[open-questions/unitary-subleading|Open: Subleading Term for Unitary Programming]]

## External References

- [Kirillov orbit method (Wikipedia)](https://en.wikipedia.org/wiki/Orbit_method)
- [Coadjoint representation / Coadjoint orbit (Wikipedia)](https://en.wikipedia.org/wiki/Coadjoint_representation)
- A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics, AMS (2004)
- [Geometric quantization (Wikipedia)](https://en.wikipedia.org/wiki/Geometric_quantization)
