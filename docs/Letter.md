# Letter: Free Entropy and Quantum Minimum Description Length

**Title:** “Free entropy and quantum minimum description length”
**Authors:** Patrick Hayden, Alexander Maloney, Jinzhao Wang, Yuxiang Yang
**Format:** PRL-style Letter with End Matter
**Current source:** [letter.tex](https://github.com/JWang226/QMDL/blob/main/letter.tex)

## Summary

The current Letter introduces a finite-dimensional, finite-resolution **physical free entropy** and relates it to the optimal memory for a known-spectrum, unknown-eigenbasis family of quantum states. The [[Article|companion Article]] supplies the compression construction and matching converse. The Letter explains the volume interpretation, fixes its additive constants, and derives the geometric formulas for general spectral multiplicities.

All logarithms are base two. The Letter's source labels below identify its statements independently of the Article's theorem numbering.

## The Main Relation

For fixed dimension $d$ and rank $r$, with distinct positive eigenvalues $p_1>\cdots>p_r>0$ and all remaining eigenvalues zero, an attaining code sequence has

$$
|M_n|=\log_2\dim M_n
=\frac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1).
$$

Set $N_\rho=r(2d-r-1)$ and $\kappa=(d-r)^2+r$. The offset is

$$
C_{d,r}
=-\frac12\sum_{k=d-r}^{d-1}\log_2(k!)
-\frac{N_\rho}{4}\log_2 2
-\frac12\log_2\frac{\Gamma(d^2/2+1)}{\Gamma(\kappa/2+1)}.
$$

It depends only on dimension and rank, not on the distinct positive eigenvalues. The memory cost includes all retained quantum and classical registers. The channels may depend on the spectrum and $n$, but not on the unknown unitary, and must recover the whole $n$-copy state with vanishing global trace-distance error.

The main text states the full-rank case in [eq:result](https://github.com/JWang226/QMDL/blob/main/letter.tex#L208) and [eq:result_const](https://github.com/JWang226/QMDL/blob/main/letter.tex#L212). The End Matter extends it to rank-deficient states after [eq:rank_def_qmdl](https://github.com/JWang226/QMDL/blob/main/letter.tex#L404).

The resolution $n^{-1}$ belongs to this volume comparison. It is **not** the angular statistical distinguishability scale $n^{-1/2}$. Replacing one by the other in the displayed formula would change its leading coefficient.

## What Is Being Counted?

The Letter compares three counting constructions:

| Quantity | What is counted | Normalization or task |
| --- | --- | --- |
| Shannon entropy | Typical strings | Log count per symbol |
| Voiculescu's microstate free entropy | Hermitian matrices matching a tracial distribution's moments | Large matrix-size volume with a universal normalization |
| Physical free entropy | Resolution cells in a tube around a fixed finite-dimensional unitary orbit | Exact Hilbert–Schmidt tube-volume/reference-ball ratio |

The last quantity is nonnegative and is zero precisely for scalar operators. It is defined in the full Hermitian matrix space, so the tube can contain matrices that are not density operators. Covering-number logarithms agree with it only up to an $O(1)$ ambiguity at fixed dimension; the volume-ratio convention fixes that ambiguity.

The [[concepts/physical-free-entropy|physical free entropy page]] gives the constants and rank-deficient formulas. The [[concepts/free-entropy|free entropy page]] explains why the usual large-matrix entropy is $-\infty$ for an atomic finite-dimensional spectral measure.

## Structure and Source Map

| Topic | Source label | Wiki guide |
| --- | --- | --- |
| Shannon typical-string count | [eq:shannon](https://github.com/JWang226/QMDL/blob/main/letter.tex#L86) | [[concepts/free-probability-and-entropy|Introduction to the entropy constructions]] |
| Schumacher typical-subspace expression | [eq:vN](https://github.com/JWang226/QMDL/blob/main/letter.tex#L94) | [[concepts/schumacher-compression|Schumacher compression]] |
| Matrix microstates and logarithmic energy | [eq:free_ent](https://github.com/JWang226/QMDL/blob/main/letter.tex#L106), [eq:free_ent_formula](https://github.com/JWang226/QMDL/blob/main/letter.tex#L125) | [[concepts/free-entropy|Voiculescu's free entropy]] |
| Exact physical entropy definition | [eq:free_phys_def](https://github.com/JWang226/QMDL/blob/main/letter.tex#L146) | [[concepts/physical-free-entropy|Physical free entropy]] |
| Orbit dimension and regularized spectral term | [eq:free_phys](https://github.com/JWang226/QMDL/blob/main/letter.tex#L156), [eq:reg_free_ent](https://github.com/JWang226/QMDL/blob/main/letter.tex#L161) | [[concepts/free-entropy-dimension|Free entropy dimension]] |
| Full-rank optimal memory | [eq:result_qmdl](https://github.com/JWang226/QMDL/blob/main/letter.tex#L201) | [[results/achievability|Achievability]] and [[results/converse|converse]] |
| Weyl product and geometric interpretation | [eq:weyl_geometry](https://github.com/JWang226/QMDL/blob/main/letter.tex#L228) | [[concepts/weyl-dimension-formula|Weyl dimension formula]] |
| Exact Hilbert–Schmidt constants | [eq:hs_volume_element](https://github.com/JWang226/QMDL/blob/main/letter.tex#L285), [eq:free_phys1_app](https://github.com/JWang226/QMDL/blob/main/letter.tex#L298) | [[concepts/physical-free-entropy|Volume derivation]] |
| Qualified double-scaling bridge | [rem:bridge](https://github.com/JWang226/QMDL/blob/main/letter.tex#L314), [eq:bridge](https://github.com/JWang226/QMDL/blob/main/letter.tex#L316) | [[concepts/physical-free-entropy|Relation to the large-dimension entropy]] |
| General spectral multiplicities | [eq:degenerate_volume](https://github.com/JWang226/QMDL/blob/main/letter.tex#L367), [eq:degenerate_free_ent](https://github.com/JWang226/QMDL/blob/main/letter.tex#L380) | [[open-questions/degenerate-spectrum|Geometry versus the remaining operational question]] |

## Scope and Open Directions

The Letter derives the physical-entropy geometry for arbitrary multiplicities. Its QMDL relation is established for spectra whose positive eigenvalues are distinct, including pure and rank-deficient states. Extending the optimal memory relation through its constant to arbitrary repeated positive eigenvalues is stated as an expectation in the End Matter.

The discussion also proposes broader operator-programming and multivariable free-entropy connections. It does not identify QMDL with a machine-dependent quantum Kolmogorov complexity, prove a general programming theorem, or extend the standard tracial definition directly to type III algebras.

The checked Lean endpoints concern [[Article|Article Theorems 1 and 2]]: fixed-spectrum optimal memory and finite cloning accuracy. They establish the compression side used by the Letter. The Letter's tube-volume identities, normalization constants, double-scaling bridge, and conjectural extensions are **not** thereby formalized. See [[formalization|formalization scope]] and [[proof-structure|the checked proof structure]].

## Related

- [[concepts/free-probability-and-entropy|Free probability and the entropy constructions]]
- [[concepts/physical-free-entropy|Physical free entropy]]
- [[concepts/quantum-minimum-description-length|Quantum minimum description length]]
- [[open-questions/free-entropy-conjecture|Broader programming conjecture]]
