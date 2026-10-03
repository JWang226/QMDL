# Flag Manifold

**Appears in:** the current [[Letter|Letter]] and [[Article|Article]].
**Source labels:** [eq:degenerate_free_ent](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L380), [eq:weyl_geometry](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L228), [eq:rank_def_qmdl](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex#L404).

## Definition

For positive block sizes $g_1,\ldots,g_m$ with $\sum_a g_a=d$, the partial flag manifold is

$$
\mathrm{Fl}(g_1,\ldots,g_m)
=\mathrm U(d)/\bigl(\mathrm U(g_1)\times\cdots\times\mathrm U(g_m)\bigr).
$$

Its real dimension is

$$
N_\rho=d^2-\sum_a g_a^2
=2\sum_{a<b}g_ag_b.
$$

## Intuition

The flag manifold parameterizes the ordered eigenspaces of a Hermitian operator with fixed distinct spectral levels and multiplicities $g_a$. Equivalently, it is the operator's unitary orbit. It does not retain a choice of basis within each eigenspace: the stabilizer factors $\mathrm U(g_a)$ identify rotations that leave the operator unchanged.

The dimension follows by subtracting the stabilizer's $\sum_a g_a^2$ real parameters from the $d^2$ parameters of $\mathrm U(d)$.

## Special Cases

- **Full flag:** all $g_a=1$. The orbit is $\mathrm U(d)/\mathrm U(1)^d$, of real dimension $d(d-1)$.
- **Grassmannian:** two distinct spectral levels of multiplicities $k$ and $d-k$. The orbit is the space of $k$-dimensional subspaces of $\mathbb C^d$, of real dimension $2k(d-k)$.
- **Rank $r$ with distinct positive eigenvalues:** each positive level is simple, and zero has multiplicity $d-r$ when $r<d$. The dimension is $r(2d-r-1)$.
- **Scalar operator:** one block of size $d$. The orbit is a point and has dimension zero.

## Qutrit Examples and Their Scope

For $p_1>p_2>0=p_3$, all three spectral levels are distinct. The stabilizer is $\mathrm U(1)^3$, so the rank-two qutrit orbit is the full flag manifold, with real dimension $9-3=6$. A full-rank qutrit with three distinct eigenvalues has the same orbit dimension.

For both cases, the Article's theorem gives an attaining memory cost

$$
|M_n|=3\log_2 n+O(1),
\qquad |M_n|:=\log_2\dim M_n,
$$

with the spectrum-dependent constant specified in the theorem. The equal leading coefficients do not imply equal order-one terms.

For the normalized rank-two projector

$$
\rho=\tfrac12\bigl(|0\rangle\langle0|+|1\rangle\langle1|\bigr),
$$

the spectrum $(1/2,1/2,0)$ has multiplicities $(2,1)$. Its orbit is $\mathrm{Gr}(2,3)$, with real dimension $9-4-1=4$. The Letter's tube-volume expansion applies and gives a leading physical-entropy term $4\log_2\varepsilon^{-1}$.

The predicted memory coefficient is therefore $2\log_2 n$, but this example has **repeated positive eigenvalues** and lies outside the Article's stated and Lean-checked QMDL theorem. The Letter describes the general multiplicity-dependent QMDL relation as an expected extension; see [[open-questions/degenerate-spectrum|the degenerate-spectrum question]].

## Hilbert–Schmidt and KKS Volume Forms

A flag manifold is a coadjoint orbit of $\mathrm U(d)$. The [[concepts/kks-theorem|Kirillov–Kostant–Souriau construction]] equips it with a symplectic form.

For distinct eigenvalues, the two real tangent directions associated with a pair $(i,j)$ each acquire an eigenvalue-gap factor in the induced Hilbert–Schmidt metric. Thus Hilbert–Schmidt orbit volume carries

$$
\Delta(p)^2,\qquad \Delta(p)=\prod_{i<j}(p_i-p_j).
$$

The KKS form treats those directions as one canonical pair, contributing one gap to symplectic volume and giving $\Delta(p)$. For multiplicities $g_a$, the corresponding inter-level factors have exponents $2g_ag_b$ and $g_ag_b$, respectively.

These different exponents explain the factor of one half in the entropy comparison. They do **not** give a literal identity between representation dimension and the square root of Hilbert–Schmidt volume. Normalization constants, integral-weight shifts, and the tube's reference-cell volume must also be included. The [[concepts/vandermonde-determinant|Vandermonde page]] records these distinctions.

For the spectra covered by the Article, the attaining code satisfies

$$
|M_n|=\frac{N_\rho}{2}\log_2 n+O(1)
=\frac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1).
$$

The second equality uses the Letter's explicit volume calculation and offset. Here $n^{-1}$ is the resolution in the volume comparison, distinct from the $n^{-1/2}$ angular distinguishability scale.

## Free Entropy Dimension and Formal Scope

For the finite-dimensional atomic spectral distribution with multiplicities $g_a$, the Letter cites

$$
\delta(\rho)=1-\frac1{d^2}\sum_a g_a^2,
\qquad N_\rho=d^2\delta(\rho).
$$

This identifies an operator-algebraic dimension with the normalized orbit dimension. The Letter's geometry permits arbitrary multiplicities. The Article's Lean endpoints prove the memory and cloning statements for distinct positive eigenvalues, allowing a repeated zero eigenvalue; they do not formalize the flag-manifold geometry or establish the conjectured QMDL extension to repeated positive levels.

## Related

- [[concepts/free-entropy-dimension|Free entropy dimension]]
- [[concepts/physical-free-entropy|Physical entropy and tube volumes]]
- [[concepts/kks-theorem|KKS symplectic form]]
- [[concepts/quantum-minimum-description-length|Quantum minimum description length]]
- [[concepts/weyl-dimension-formula|Weyl dimension formula]]
- [[open-questions/degenerate-spectrum|QMDL with repeated positive eigenvalues]]
