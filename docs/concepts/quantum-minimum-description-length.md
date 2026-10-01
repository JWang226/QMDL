# Quantum Minimum Description Length (QMDL)

**Appears in:** [[Letter]], [[Article]]

## Intuition

Given $n$ copies of a density matrix $\rho^{\otimes n}$, how small a quantum memory do you need to store a faithful description? This is NOT Schumacher compression (which preserves purifications). QMDL compression only needs to recover the **state itself**, not its correlations with a reference system.

Concretely: you know the spectrum of $\rho$ (its eigenvalues), but not its eigenbasis. You want to compress $\rho^{\otimes n}$ into a quantum memory $M_n$ such that you can later decompress and recover $\rho^{\otimes n}$ with high fidelity.

The key insight is that since the spectrum is known, you only need to store the **eigenbasis** -- a point on a continuous manifold. The memory cost should therefore scale as $O(\log n)$ (not $O(n)$ like Schumacher), with the coefficient determined by the dimension of this manifold.

## The Compression Task

Write $m_n=\dim M_n$ for the memory dimension and $|M_n|=\log_2 m_n$ for its cost, following the current Article. An encoder and decoder are CPTP maps between the physical $n$-copy space and $M_n$. They may depend on $n$ and the known spectrum, but not on the unknown unitary $g$.

The reliability criterion is

$$\delta_n=\sup_{g\in U(d)}\frac12\|\mathcal D_n\mathcal E_n(\rho_g^{\otimes n})-\rho_g^{\otimes n}\|_1\longrightarrow0.$$

Any retained classical register is included in the memory dimension. The converse also holds under the weaker requirement that the Haar-average error tends to zero.

## Key Distinction from Schumacher Compression

| | Schumacher | QMDL |
|---|---|---|
| Preserves purification? | Yes | No |
| Rate (leading order) | $nS(\rho)$ | $O(\log n)$ |
| What is retained | State and reference correlations | Quantum description sufficient to recover the orbit state |
| Entropy notion | von Neumann entropy | Free entropy |

The QMDL rate is only $O(\log n)$ because knowing the spectrum means you only need to describe the eigenbasis, which lives on a [[concepts/flag-manifold|Flag Manifold]] of dimension $r(2d-r-1)$ (when spectrum is non-degenerate with rank $r$).

## Main Result

For $\rho$ of rank $r$ with non-degenerate positive eigenvalues $x_1 > \cdots > x_r > 0$:

$$|M_n| = \frac{r(2d - r - 1)}{2}\log n + \sum_{i < j \leq r} \log(x_i - x_j) + (d-r)\sum_{i=1}^r \log x_i - \sum_{k=d-r}^{d-1} \log k! + o(1)$$

The first term ($\propto \log n$) is governed by [[concepts/free-entropy-dimension|Free Entropy Dimension]]. The second-order terms ($O(1)$) are governed by [[concepts/free-entropy|regularized free entropy]]. Together they equal $\frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1/2})$ plus universal constants.

## Proof Strategy: Achievability

The encoding protocol generalizes the Yang-Chiribella-Hayashi (YCH) scheme from qubits to qudits using the [[concepts/generalized-cloning-map|Generalized Cloning Map]].

### Encoding

1. **Schur transform.** Apply $V_{\mathrm{Schur}}$ to decompose $\rho^{\otimes n}$ into Schur-Weyl sectors:
$$\rho^{\otimes n} \simeq \bigoplus_\lambda q_\lambda (\rho_\lambda \otimes \tau_\lambda)$$

2. **Measure $\lambda$.** Perform a non-demolition measurement of the Young diagram label, obtaining some $\lambda$.

3. **Discard $M_\lambda$.** Throw away the multiplicity register $\tau_\lambda$ (it is maximally mixed and carries no information about the eigenbasis).

4. **Clone to target.** Apply the generalized cloning map $C_{\lambda \to \Lambda^*}$ to map $\rho_\lambda$ into a fixed target irrep $\Lambda^*$. Store the result in a quantum memory of dimension $d_{\Lambda^*}$.

### Target irrep construction

For the coordinatewise [[definitions/typical-set|typical window]] $\epsilon_n=\sqrt{n/2}\log n$, set

$$\Lambda_i=\lceil nx_i+(r-i+1)(2\epsilon_n+1)\rceil\quad(1\le i\le r),
\qquad \Lambda_i=0\quad(i>r).$$

This makes $\Lambda-\lambda$ dominant and nonnegative for every typical $\lambda$, including the positive-to-zero boundary. It also gives $\|\Lambda-\lambda\|_1=O(\sqrt n\log n)$.

### Decoding and error

The decoder samples a sector from the known spectrum-dependent distribution, applies the reverse cloner, appends its maximally mixed multiplicity register, and reconstructs the physical state. Replacement channels handle atypical sectors. The forward and reverse typical errors plus twice the atypical mass bound the total error:

$$\delta_n\le\epsilon_{\mathrm{forward},n}+\epsilon_{\mathrm{reverse},n}
+2\operatorname{Pr}(\text{atypical})
=O\!\left(\frac{\log n}{\sqrt n}\right).$$

The current Theorem 2 gives trace distance directly, without the square-root conversion in the older Notes' fidelity argument. The actual physical tail and actual CPTP maps are proved in Lean; no supplied Schur decomposition or concentration premise remains in the final result.

The actual canonical target dimension satisfies $\log_2\dim H_\Lambda=L_{d,r}(n,x)+o(1)$, including its additive constant. The proof establishes the canonical Weyl character and dimension identities before taking this asymptotic limit.

## Proof Strategy: Converse

Transfer an arbitrary code for $\rho_g^{\otimes n}$ to the padded canonical orbit using the actual comparison channels in reverse order around that code. Contractivity and the triangle inequality bound its Haar-average error by the physical code error plus the two comparison errors.

The irreducible-orbit memory theorem then gives

$$\dim M_n\ge\dim H_{\Lambda_n}
\left(1-\frac{\overline\delta_n+o(1)}{\gamma_x'}\right),$$

where $\gamma_x'>0$ depends only on the fixed spectrum and dimension. Taking logarithms and using the exact canonical dimension asymptotics yields

$$\liminf_{n\to\infty}\bigl(|M_n|-L_{d,r}(n,x)\bigr)\ge0.$$

The current Lean proof uses a proved uniform gap sufficient for this limit; it need not reproduce the Article's sharper displayed gap constant. The gap, irreducibility, channels, and transfer error are derived, not assumed in `FreeEntropy.theorem1_converse`.

## Formal Scope

`Theorem1Complete` contains achievability, the Haar-average converse, and its worst-case-error corollary for every permitted dimension and rank. This includes rank-deficient sources, pure states, and the trivial one-dimensional case. Repeated **positive** eigenvalues and unknown spectra are outside this fixed-spectrum endpoint. See [[proof-structure]] and [[open-questions/degenerate-spectrum]].

## Related

- [[concepts/free-entropy|Free Entropy]] -- the information-theoretic quantity that governs QMDL
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- governs the leading $\log n$ coefficient
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- the representation-theoretic decomposition
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- the key technical tool for achievability
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] -- converts irrep dimensions to the QMDL rate
- [[concepts/flag-manifold|Flag Manifold]] -- the geometric space whose dimension appears
- [[concepts/koashi-imoto|Koashi-Imoto Structure]] -- exact-compression context and distinction from the quantitative converse
- [[concepts/schumacher-compression|Schumacher Compression]] -- the contrasting task that preserves purifications

## External References

- [Minimum description length (Wikipedia)](https://en.wikipedia.org/wiki/Minimum_description_length)
- [Rissanen, "Modeling by shortest data description" (1978)](https://doi.org/10.1016/0005-1098(78)90005-5)
- [Schumacher, "Quantum coding" (1995)](https://doi.org/10.1103/PhysRevA.51.2738)
- M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge University Press (2000)
