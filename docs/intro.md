# Introduction

**Project:** Free Entropy and Quantum Minimum Description Length

**Authors:** Patrick Hayden, Alexander Maloney, Jinzhao Wang, Yuxiang Yang

This wiki explains the mathematical project and the current Lean proof of
Theorems 1 and 2 in the bundled
[Article source](https://github.com/JWang226/QMDL/blob/main/article.tex).
Start with the results below, then follow [[proof-structure|the proof map]]
for their dependencies or [[formalization|the verification guide]] to check
this formalization yourself. The current
[Letter source](https://github.com/JWang226/QMDL/blob/main/letter.tex)
develops the entropy interpretation below. [[Notes]] retains historical
programming material. These broader claims are not all covered by the Lean proof.

## The compression problem

Suppose the spectrum of a density matrix is known, but its eigenbasis is
unknown. A single pair of quantum channels must compress and recover
$\rho_U^{\otimes n}$ for every $U\in\mathrm U(d)$, where
$\rho_U=U\operatorname{diag}(x)U^\dagger$. The retained memory includes
any classical register. Its cost is $\log_2\dim M_n$.

The task only asks to recover the state itself. [[concepts/schumacher-compression|Schumacher compression]]
also preserves correlations with a reference and has a different cost.
Here, $O(\log n)$ quantum memory suffices. This does not make the protocol
purely classical: for a nontrivial orbit, tomography followed by state
preparation cannot give vanishing global reconstruction error.

## Theorem 1: optimal memory, including the constant

Fix dimension $d$, rank $1\le r\le d$, and distinct positive eigenvalues
$x_1>\cdots>x_r>0$ with sum one; the remaining eigenvalues are zero. Define

$$
L_{d,r}(n,x)=\frac{r(2d-r-1)}2\log_2 n
+\sum_{1\le i<j\le r}\log_2(x_i-x_j)
+(d-r)\sum_{i=1}^r\log_2 x_i
-\sum_{k=d-r}^{d-1}\log_2(k!).
$$

[[results/achievability|Achievability]] constructs encoders and decoders,
independent of $U$, with

$$
\log_2\dim M_n=L_{d,r}(n,x)+o(1),\qquad
\sup_U\frac12\|\rho_U^{\otimes n}-\mathcal D_n\mathcal E_n(\rho_U^{\otimes n})\|_1
=O\!\left(\frac{\log n}{\sqrt n}\right).
$$

[[results/converse|The converse]] proves that any physical code sequence
whose Haar-average reconstruction error vanishes obeys

$$
\liminf_{n\to\infty}\bigl(\log_2\dim M_n-L_{d,r}(n,x)\bigr)\ge0.
$$

This also covers vanishing worst-case error. The result concerns fixed
$d$ and fixed $x$; it makes no uniform assertion as eigenvalues collide,
and does not prescribe the optimal memory for every chosen error schedule.
The scalar case $d=1$ and rank-one states are included.

The coefficient $r(2d-r-1)/2$ is **half** the real dimension of the
[[concepts/flag-manifold|unitary orbit]]. The spectral terms are half the
logarithm of its Hilbert–Schmidt volume, up to a constant depending on $d,r$.
The current [[Letter]] makes this connection precise using its
[[definitions/physical-free-entropy-def|physical free entropy]]:

$$
\chi_{\mathrm{phy}}(\rho;\varepsilon)
=\log_2\frac{\operatorname{Vol}(\Omega_\varepsilon)}
{\operatorname{Vol}(B_\varepsilon^{d^2})},
\qquad
\Omega_\varepsilon=\{X=X^\dagger:\|\lambda(X)-p\|_2\le\varepsilon\}.
$$

This is an ambient Hilbert–Schmidt tube-volume ratio. Its additive constant
is fixed by that convention; covering-number entropy agrees only up to
$O(1)$. For the attaining sequence and the spectra above, the Letter gives

$$
\log_2\dim M_n=\tfrac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1),
$$

where, with $N_\rho=r(2d-r-1)$ and $\kappa=(d-r)^2+r$,

$$
C_{d,r}=-\frac12\sum_{k=d-r}^{d-1}\log_2(k!)
-\frac{N_\rho}{4}\log_2 2
-\frac12\log_2\frac{\Gamma(d^2/2+1)}{\Gamma(\kappa/2+1)}.
$$

Here $n^{-1}$ is the resolution in the volume comparison; the local
statistical distinguishability scale is $n^{-1/2}$. The memory formula is
covered by the Article certificates. The tube-volume derivation, offset
identity and conditional large-dimension bridge in the Letter are separate
manuscript results without current Lean certificates. Ordinary Voiculescu
entropy of a finite atomic spectrum is $-\infty$, so it cannot replace this
finite-resolution definition.

## Theorem 2: the finite cloning estimate

The technical input is [[results/cloning-fidelity|a trace-distance bound in both directions]]
for the generalized cloning channels. Fix $d\ge2$ and the same normalized
rank-$r$ spectrum. If $\mu,\nu$ are partitions vanishing beyond the first
$r$ rows and $\nu-\mu$ is dominant, their errors are at most

$$C_{d,x}\frac{\|\nu-\mu\|_1}{b_\mu+1},$$

where $b_\mu$ is the minimum supported adjacent-row gap. Dominance does
not require every entry of the difference to be nonnegative. The formal
proof constructs actual CPTP maps and identifies them with the original
normalized Choi-projector formulas; its reverse map is also identified with
the Petz formula. Rank one and equal rows are covered.

## How the proofs fit together

The [[proof-structure|proof map]] gives the full route. Its central steps are:

1. Construct canonical irreducible representations and identify the physical
   tensor-power sectors with them; prove the required character, dimension,
   weight and covariance facts.
2. Prove the finite cloning bound directly in trace distance, then identify
   the Cartan, Choi and Petz descriptions of the channels.
3. Concentrate the physical source on typical sectors and send them to one
   padded target representation. Here $\|\nu-\mu\|_1=O(\sqrt n\log n)$ and
   $b_\mu=\Omega(n)$, yielding the stated uniform error rate. Explicit
   replacement channels handle atypical sectors.
4. Evaluate the target's dimension through its additive constant. For the
   converse, combine a uniform positive spectral gap with the quantitative
   Haar-orbit memory bound and transfer arbitrary physical codes to that orbit.

This converse uses the quantitative incompressibility argument proved in the
library; merely citing the exact-reconstruction Koashi–Imoto theorem would
not establish the required vanishing-error lower bound through its constant.

## Wider project and reading routes

| Source | Role | Formalization boundary |
| --- | --- | --- |
| [[Article]] | Current full proof, including generalized cloning and optimal known-spectrum memory | Theorems 1 and 2 and their required supporting development are formalized. |
| [[Letter]] | Current finite-resolution entropy definition, geometric derivation and compression interpretation | Memory formulas follow the Article endpoints; volume and bridge claims are not separately formalized. |
| [[Notes]] | Historical extended material, including programming questions | These extensions are not automatically certified by the Article formalization. |

- [[index|Wiki index]]: results, concepts and supporting lemmas.
- [[proof-structure|Current proof structure]]: dependency diagram and Lean module map.
- [[formalization|Formalization and reproduction]]: checked scope and how to rerun the checkers.
- [[notation|Notation]]: memory cost, error conventions, rows and spectral parameters.
- [[open-questions/free-entropy-conjecture|Broader questions]]: entropy and programming extensions outside the formalized scope.
