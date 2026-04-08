# Notation Glossary

Central reference for all notation used across the three papers.

## Quantum States and Operators

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\rho$ | Density matrix (state) on $\mathbb{C}^d$ | All papers |
| $\rho^{\otimes n}$ | $n$ i.i.d. copies of $\rho$ | All papers |
| $p_1 > p_2 > \cdots > p_r > 0$ | Eigenvalues of $\rho$ (Letter, Notes) | Letter, Notes |
| $x_1 > x_2 > \cdots > x_r > 0$ | Eigenvalues of $\rho$ (Article) | Article |
| $r = \mathrm{rank}(\rho)$ | Rank of the state | All papers |
| $d$ | Hilbert space dimension | All papers |
| $F(\rho, \sigma)$ | Fidelity: $\|\sqrt{\rho}\sqrt{\sigma}\|_1$ (unsquared) | Article, Notes |

## Representation Theory

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\lambda, \mu, \nu$ | Partitions / highest weights of $\mathrm{GL}(d,\mathbb{C})$ irreps | All papers |
| $H_\lambda$ | $\mathrm{GL}(d,\mathbb{C})$ irreducible representation with highest weight $\lambda$ | Article, Notes |
| $M_\lambda$ | Symmetric group $S_n$ irreducible representation (multiplicity space) | Article, Notes |
| $d_\lambda = \dim H_\lambda$ | Dimension of GL irrep | All papers |
| $s_\lambda(x)$ | Schur polynomial: $\mathrm{Tr}[\pi_\lambda(\mathrm{diag}(x))]$ | All papers |
| $K_{\lambda,w}$ | Kostka number: multiplicity of weight $w$ in $H_\lambda$ | Article, Notes |
| $\omega = (\nu - \mu)^+$ | PRV component: dominant weight in $\mu^* \otimes \nu$ | Article, Notes |
| $\Pi_\omega$ | Projector onto the PRV component in $\nu \otimes \mu^*$ | Article, Notes |
| $V: H_\nu \to H_\mu \otimes H_\omega$ | Intertwining isometry from PRV decomposition | Article, Notes |
| $\rho_\lambda$ | Normalized GL irrep: $\pi_\lambda(\rho)/s_\lambda(x)$ | Article, Notes |
| $V_{\text{Schur}}$ | Schur transform isometry: $(\mathbb{C}^d)^{\otimes n} \to \bigoplus_\lambda H_\lambda \otimes M_\lambda$ | All papers |

## Young Diagrams and Partitions

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\|\lambda\| = \sum_i \lambda_i$ | Size of partition | All papers |
| $\|\lambda\|_\infty = \lambda_1 - \lambda_d$ | Width of Young diagram | Article, Notes |
| $g_\lambda = \min_i(\lambda_i - \lambda_{i+1})$ | Edge gap of partition | Article, Notes |
| $\delta \in Q_+$ | Weight offset (in positive root lattice) | Article, Notes |
| $\alpha_i = e_i - e_{i+1}$ | Simple roots of type $A_{d-1}$ | Article, Notes |
| $\Phi^+$ | Set of positive roots | Article, Notes |
| $d(\mu, \nu) = \sum_i |\mu_i - \nu_i|$ | Distance between irreps | Article |

## Free Entropy Quantities

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\chi(a)$ | Voiculescu's free entropy of operator $a$ | Letter, Notes |
| $\chi_{\mathrm{phy}}(\rho; \varepsilon)$ | Physical free entropy at resolution $\varepsilon$ | Letter, Notes |
| $\chi_{\mathrm{reg}}(\rho)$ | Regularized free entropy: $2\sum_{i<j} \log|p_i - p_j|$ | Letter, Notes |
| $\delta(a)$ | Free entropy dimension | Letter, Notes |
| $N(\Omega, \varepsilon)$ | $\varepsilon$-covering number | Letter, Notes |
| $\Omega_\varepsilon$ | Set of Hermitian matrices spectrally $\varepsilon$-close to $\rho$ | Letter |

## Compression

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $(E, D)$ | Encoder-decoder pair | All papers |
| $|M|$ or $|M_n|$ | Memory size (dimension of compressed system) | All papers |
| $\delta_n$ | Compression error: $\frac{1}{2}\|\rho^{\otimes n} - D \circ E(\rho^{\otimes n})\|_1$ | All papers |
| QMDL | Quantum Minimum Description Length | All papers |

## Cloning Map

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $C_{\mu \to \nu}$ | Generalized cloning map from $H_\mu$ to $H_\nu$ | Article, Notes |
| $J_\omega$ | Choi operator: $(d_\mu/d_\omega)\Pi_\omega$ | Article, Notes |

## Asymptotics

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $\xi = \min_i(\ln x_i - \ln x_{i+1})$ | Logarithmic spectral gap | Article |
| $\xi_n = \sqrt{2n}\log n + 1$ | Padding parameter for typical set | Article |
| $T_{p,n}$ | Typical set of Young diagrams near $np$ | Article |

## Unitary & Observable Programming

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $D$ | Program register dimension | Notes |
| $\varepsilon$ | Programming error (diamond norm) | Notes |
| $f$ | Number of parameters in the unitary/observable family | Notes |
| $\{U_x\}_{x \in \mathbb{R}^f}$ | Parameterized family of unitaries | Notes |
| $|\mathrm{sin}_y\rangle$ | Sine state for phase estimation | Notes |
| $\mathbb{T}^f$ | $f$-dimensional torus (parameter space) | Notes |
| $\|\cdot\|_\diamond$ | Diamond norm (completely bounded trace norm) | Notes |
| $H$ | Hermitian observable | Notes (Sec. 9) |
| $g_1, \ldots, g_m$ | Multiplicities of distinct eigenvalues of $H$ | Notes (Sec. 9) |
| $\mathrm{Fl}(g_1, \ldots, g_m)$ | Flag manifold $U(d)/(U(g_1) \times \cdots \times U(g_m))$ | Notes |

## Representation Theory (Additional)

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $C_2$ | Quadratic Casimir operator | Article, Notes |
| $\mathfrak{K}(\delta)$ | Kostant partition function | Article, Notes |
| $\rho_W = (d-1, d-2, \ldots, 0)$ | Weyl vector | Article, Notes |
| $W$ | Weyl group of $\mathrm{GL}(d)$ | Article, Notes |
| $w_0$ | Longest element of the Weyl group | Article, Notes |
| $\mu^* = (-\mu_d, \ldots, -\mu_1)$ | Contragredient (dual) highest weight | Article, Notes |
| $\Delta(x) = \prod_{i<j}(x_i - x_j)$ | Vandermonde determinant | All papers |
| $p_\mu(\delta) = x^{\mu-\delta}/s_\mu(x)$ | Weight probability in normalized irrep | Article, Notes |
| $m_\mu(\delta) = K_{\mu, \mu-\delta}$ | Weight multiplicity (Kostka number) | Article, Notes |

## Random Matrix / Free Probability

| Symbol | Meaning | Defined in |
|--------|---------|------------|
| $M_N^{\mathrm{s.a.}}$ | Set of $N \times N$ self-adjoint matrices | Letter, Notes |
| $(A, \tau)$ | Tracial von Neumann algebra | Letter, Notes |
| $\mu_a$ | Spectral measure of operator $a$ | Letter, Notes |
| $s$ | Standard semicircular element | Letter, Notes |
| $\Gamma(a; m, \varepsilon, N)$ | Microstate space (matrices approximating $a$) | Letter, Notes |
