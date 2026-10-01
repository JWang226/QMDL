# Notation Glossary

Central reference for the current [[Article]] and [[Letter]], with historical [[Notes]] conventions identified separately. Article theorem numbering takes precedence for the Lean endpoints; Letter results use equation labels. See [[proof-structure]]. Both current manuscripts use base-two logarithms; $\ln$ and $\exp$ denote natural logarithms and exponentials.

## Quantum States and Operators

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\rho$ | Density matrix (state) on $\mathbb{C}^d$ | All papers |
| $\rho^{\otimes n}$ | $n$ i.i.d. copies of $\rho$ | All papers |
| $p_1 > p_2 > \cdots > p_r > 0$ | Eigenvalues of $\rho$ (Letter, Notes) | Letter, Notes |
| $x_1 > x_2 > \cdots > x_r > 0$ | Eigenvalues of $\rho$ (Article) | Article |
| $r = \mathrm{rank}(\rho)$ | Rank of the state | All papers |
| $d$ | Hilbert space dimension | All papers |
| $T(\rho,\sigma)=\frac12\Vert\rho-\sigma\Vert_1$ | Trace distance; actual matrix trace norm in Lean | Article, `TraceDistance` |
| $F(\rho, \sigma)$ | Fidelity: $\Vert\sqrt{\rho}\sqrt{\sigma}\Vert_1$ (unsquared) | Article, Notes |

## Representation Theory

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\lambda, \mu, \nu$ | Dominant highest rows; source/target rows in Theorem 2 are nonnegative partitions supported on the first $r$ entries | Article |
| $H_\lambda$ | $\mathrm{GL}(d,\mathbb{C})$ irreducible representation with highest weight $\lambda$ | Article, Notes |
| $M_\lambda$ | Symmetric group $S_n$ irreducible representation (multiplicity space) | Article, Notes |
| $\mathcal K_\lambda$ | Same permutation multiplicity space, denoted $M_\lambda$ in the Article | Letter |
| $d_\lambda = \dim H_\lambda$ | Dimension of GL irrep | All papers |
| $s_\lambda(x)$ | Schur polynomial: $\mathrm{Tr}[\pi_\lambda(\mathrm{diag}(x))]$ | All papers |
| $K_{\lambda,w}$ | Kostka number: multiplicity of weight $w$ in $H_\lambda$ | Article, Notes |
| $\omega = (\nu - \mu)^+$ | PRV highest weight; Theorem 2 assumes $\nu-\mu$ already dominant, possibly signed | Article, Notes |
| $\Pi_\omega$ | Projector onto the PRV component in $\mu^* \otimes \nu$ | Article, Notes |
| $V: H_\nu \to H_\mu \otimes H_\omega$ | Cartan embedding when $\nu=\mu+\omega$ with dominant $\omega$ | Article, Notes |
| $\rho_\lambda$ | Normalized GL irrep: $\pi_\lambda(\rho)/s_\lambda(x)$ | Article, Notes |
| $V_{\text{Schur}}$ | Schur transform isometry: $(\mathbb{C}^d)^{\otimes n} \to \bigoplus_\lambda H_\lambda \otimes M_\lambda$ | All papers |

## Young Diagrams and Partitions

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\lvert\lambda\rvert=\sum_i\lambda_i$ | Partition size; for signed weights, the ordinary sum is not an $L^1$ norm | Article |
| $\lambda_1-\lambda_d$ | Width (a historical Notes convention for $\Vert\lambda\Vert$); distinct from the current $L^1$ norm | Notes |
| $b_\mu=\min_{1\le i\le\min(r,d-1)}(\mu_i-\mu_{i+1})$ | Supported gap in the finite cloning bound; includes the last positive-to-zero boundary | Article Theorem 2 |
| $g_\mu=\min_{1\le i<r}(\mu_i-\mu_{i+1})$ | Internal supported gap for shallow multiplicities ($r\ge2$); Notes also uses a full-row convention | Article, Notes |
| $\delta \in Q_+$ | Weight offset (in positive root lattice) | Article, Notes |
| $\alpha_i = e_i - e_{i+1}$ | Simple roots of type $A_{d-1}$ | Article, Notes |
| $\Phi^+$ | Set of positive roots | Article, Notes |
| $D=\Vert\nu-\mu\Vert_1$ | Sum of absolute row differences; also written $d(\mu,\nu)$ in older pages | Article Theorem 2 |
| $\lvert\delta\rvert=\sum_i c_i$ for $\delta=\sum_i c_i\alpha_i$ | Root depth; distinct from the coordinate $L^1$ norm | Article |

## Free Entropy Quantities

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\chi(a)$ | Voiculescu's free entropy of operator $a$ | Letter, Notes |
| $\chi_{\mathrm{phy}}(\rho; \varepsilon)$ | Unnormalized $\log_2[\operatorname{Vol}(\Omega_\varepsilon)/\operatorname{Vol}(B_\varepsilon^{d^2})]$ | Current Letter |
| $\chi_{\mathrm{reg}}(\rho)$ | $2\sum_{i<j,\,p_i\ne p_j}\log_2\lvert p_i-p_j\rvert$; coinciding values excluded | Current Letter |
| $\delta(a)$ | Free entropy dimension | Letter, Notes |
| $N(\Omega, \varepsilon)$ | $\varepsilon$-covering number | Letter, Notes |
| $\Omega_\varepsilon$ | Ambient Hermitian tube: $\|\lambda(X)-p\|_2\le\varepsilon$; not restricted to density matrices | Letter |
| $g_a$ | Multiplicity of distinct spectral value $p_a$ in the multiplicity formulas | Letter |
| $\kappa=\sum_a g_a^2$ | Real normal dimension of the unitary orbit | Letter |
| $N_\rho=d^2-\kappa$ | Real orbit dimension; $r(2d-r-1)$ for distinct positive eigenvalues and a zero block | Letter |
| $g=\min_{a\ne b}\lvert p_a-p_b\rvert$ | Minimum distinct spectral gap; $g=\infty$ for scalar operators | Letter |
| $C_{d,r}$ | Spectrum-independent offset in $\log_2\dim M_n=\tfrac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1)$ for an attaining sequence | Letter |

## Compression

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $(E, D)$ | Encoder-decoder pair | All papers |
| $m_n=\dim M_n$ | Memory dimension; represented by `memory n : ℕ` in Lean | Article, Lean |
| $\lvert M_n\rvert=\log_2\dim M_n$ | Memory cost in qubits, including retained classical registers | Article, Letter |
| $\delta_n$ | Worst-case trace error over the unitary orbit | Article, Letter |
| $\overline\delta_n$ | Haar-average trace error; sufficient for the final converse | Article, Lean |
| $L_{d,r}(n,x)$ | Exact QMDL expression through its additive constant (`Weyl.qmdl`) | Article, Lean |
| QMDL | Quantum Minimum Description Length | All papers |

## Cloning Map

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $C_{\mu \to \nu}$ | Generalized cloning map from $H_\mu$ to $H_\nu$ | Article, Notes |
| $J_\omega$ | Choi operator: $(d_\mu/d_\omega)\Pi_\omega$ | Article, Notes |

## Asymptotics

The Letter's entropy comparison uses volume resolution $\varepsilon=n^{-1}$.
Local statistical distinguishability occurs at angular scale $n^{-1/2}$.
These scales play different roles; neither is the Article's unnormalized
typical-row width $\epsilon_n$ below.

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $q_x=\max_{i<r}x_{i+1}/x_i$, with $q_x=0$ for $r=1$ | Spectral ratio controlling mean depth and uniform gap | Article |
| $\xi=\min_{i<r}(\ln x_i-\ln x_{i+1})$ | Historical logarithmic-gap notation ($r\ge2$) | Notes/earlier estimates |
| $\epsilon_n=\sqrt{n/2}\log n$ | Unnormalized coordinatewise typical width | Article |
| $\xi_n = \sqrt{2n}\log n + 1$ | Padding parameter for typical set | Article |
| $\mathcal T_{x,n}$ | Supported partitions of $n$ with $\max_{i\le r}\lvert\lambda_i-nx_i\rvert\le\epsilon_n$ | Article |
| $\Lambda_i=\lceil nx_i+(r-i+1)\xi_n\rceil$ for $i\le r$; $0$ otherwise | Padded target row (one-based indexing) | Article |

## Unitary & Observable Programming

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $D$ | Program register dimension | Notes |
| $\varepsilon$ | Programming error (diamond norm) | Notes |
| $f$ | Number of parameters in the unitary/observable family | Notes |
| $\{U_x\}_{x \in \mathbb{R}^f}$ | Parameterized family of unitaries | Notes |
| $\lvert\mathrm{sin}_y\rangle$ | Sine state for phase estimation | Notes |
| $\mathbb{T}^f$ | $f$-dimensional torus (parameter space) | Notes |
| $\Vert\cdot\Vert_\diamond$ | Diamond norm (completely bounded trace norm) | Notes |
| $H$ | Hermitian observable | Notes (Sec. 9) |
| $g_1, \ldots, g_m$ | Multiplicities of distinct eigenvalues of $H$ | Notes (Sec. 9) |
| $\mathrm{Fl}(g_1, \ldots, g_m)$ | Flag manifold $U(d)/(U(g_1) \times \cdots \times U(g_m))$ | Notes |

## Representation Theory (Additional)

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $C_2$ | Quadratic Casimir operator | Article, Notes |
| $\mathfrak{K}(\delta)$ | Kostant partition function | Article, Notes |
| $\rho_W=(d-1,d-2,\ldots,0)$ | Shift used in the Weyl dimension/character formula | Article, Notes |
| $\varrho_i=(d+1-2i)/2$ | Half-sum of positive roots used in the Casimir scalar | Article |
| $W$ | Weyl group of $\mathrm{GL}(d)$ | Article, Notes |
| $w_0$ | Longest element of the Weyl group | Article, Notes |
| $\mu^* = (-\mu_d, \ldots, -\mu_1)$ | Contragredient (dual) highest weight | Article, Notes |
| $\Delta(x) = \prod_{i<j}(x_i - x_j)$ | Vandermonde determinant | All papers |
| $p_\mu(\delta)=x^{\mu-\delta}/s_\mu(x)$ | Eigenvalue on the weight block; its total probability is $m_\mu(\delta)p_\mu(\delta)$ | Article, Notes |
| $q_{\lambda,n}=s_\lambda(x)\dim M_\lambda$ | Schur-sector probability, distinct from a single block eigenvalue | Article |
| $m_\mu(\delta) = K_{\mu, \mu-\delta}$ | Weight multiplicity (Kostka number) | Article, Notes |

## Random Matrix / Free Probability

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $M_N^{\mathrm{s.a.}}$ | Set of $N \times N$ self-adjoint matrices | Letter, Notes |
| $(A, \tau)$ | Tracial von Neumann algebra | Letter, Notes |
| $\mu_a$ | Spectral measure of operator $a$ | Letter, Notes |
| $s$ | Standard semicircular element | Letter, Notes |
| $\Gamma(a; m, \varepsilon, N)$ | Microstate space (matrices approximating $a$) | Letter, Notes |

## Lean Indexing

Mathematical rows above are indexed from 1; Lean uses `Fin d` or natural indices starting at 0. `FixedSpectrum d r` records the decreasing positive spectrum and zero tail. `Channels.MatrixChannel` includes complete positivity and trace preservation, and `TraceDistance.traceDistance` is half the actual matrix trace norm. Auxiliary signed weights are realized using determinant twists; they do not impose invertibility on the polynomial source/target states.
