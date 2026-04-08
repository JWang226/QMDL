# Supporting Lemmas

This page collects the remaining supporting lemmas used in the proofs.

---

## Davis-Kahan Theorem (Lemma 6)

**Label:** `lem:davis_kahan`
**Source:** Article line ~1209; Notes line ~654

**Statement:** Let $H_0$ and $H = H_0 + V$ be Hermitian on a finite-dimensional Hilbert space. Let $S_0, S_1$ partition $\mathrm{spec}(H_0)$ with spectral gap $\Delta = \min_{\lambda \in S_0, \lambda' \in S_1} |\lambda - \lambda'|$. Let $P_0$ project onto the eigenspace of $H_0$ for $S_0$. If $\|V\| < \Delta$, then the eigenvalues of $H$ split into corresponding sets $\sigma_0(H), \sigma_1(H)$ with gap $\geq \Delta - \|V\|$, and the spectral projector $P$ of $H$ onto $\sigma_0(H)$ satisfies:

$$\sin(\theta_{\max}) \equiv \|P - P_0\| \leq \frac{\|V P_0\|}{\Delta - \|V\|}$$

where $\theta_{\max}$ is the largest principal angle between $\mathrm{Im}(P)$ and $\mathrm{Im}(P_0)$.

**Proof detail:** The projector $P$ is defined constructively via the resolvent: $P = -\frac{1}{2\pi i} \oint_\Gamma (z - H)^{-1} dz$ where $\Gamma$ encloses $S_0$ but excludes $S_1$. The condition $\|V\| < \Delta$ ensures no eigenvalue of $H$ crosses $\Gamma$, so $P$ has the same rank as $P_0$ and depends continuously on $V$. The bound uses $\|VP_0\|$ (the "restricted perturbation") rather than $\|V\|$, which can be much tighter -- this is the key feature exploited in the [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]] where $E_\alpha^{(\omega)}|\omega\rangle = 0$ kills half the perturbation.

**Role:** Applied in [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]] to bound how weight subspaces rotate under perturbation. The spectral gap $\Delta = \Theta(n)$ comes from the Casimir eigenvalue structure, while the restricted perturbation $\|VP_0\| = O(\sqrt{n|\delta|\|\omega\|})$ gives the final $O(\sqrt{|\delta|\|\omega\|/n})$ bound.

---

## Principal Angles (Lemma 4)

**Label:** `lem:principle_angles`
**Source:** Article line ~1095 (stated), ~2511 (proved)

**Statement:** For projectors $P, Q$ with $r = \min(\mathrm{rank}\, P, \mathrm{rank}\, Q)$:

$$\mathrm{Tr}\sqrt{PQP} = \sum_{i=1}^r \cos(\theta_i)$$

where $\theta_i$ are the principal angles between $\mathrm{Im}(P)$ and $\mathrm{Im}(Q)$.

**Proof detail:** Let $U, V$ be matrices whose columns are orthonormal bases for $\mathrm{Im}(P)$ and $\mathrm{Im}(Q)$. Then $P = UU^\dagger$, $Q = VV^\dagger$, and $PQP = U(U^\dagger V)(U^\dagger V)^\dagger U^\dagger$. Since $U$ has orthonormal columns, the nonzero eigenvalues of $PQP$ equal those of $(U^\dagger V)(U^\dagger V)^\dagger = M M^\dagger$, which are the squared singular values $\sigma_i^2$ of $M = U^\dagger V$. By definition, $\sigma_i = \cos\theta_i$. Taking the positive square root (since $PQP \geq 0$) gives eigenvalues $\cos\theta_i$, and the trace sums them.

**Role:** Connects fidelity to geometric angles between subspaces in [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]]. The block fidelity $F_{\mathrm{block}}(\delta) = \sqrt{d_\mu/d_\nu} \, \mathrm{Tr}\sqrt{\widetilde{\Pi}_{\nu-\delta} \Pi_{\mu-\delta}^{(\omega)} \widetilde{\Pi}_{\nu-\delta}} = \sqrt{d_\mu/d_\nu} \sum_i \cos\theta_i$.

---

## Monotonicity (Lemma 5)

**Label:** `lem:monotonicity`
**Source:** Article line ~1175 (stated), ~2545 (proved)

**Statement:** For a quantum channel $\mathcal{N}$ with Kraus operator $K$ and $\rho' = K\eta K^\dagger$ (unnormalized), for any density operator $\sigma$:

$$F(\rho', \sigma) \leq F(\mathcal{N}(\eta), \sigma)$$

**Proof detail:** Write $\mathcal{N}(\eta) = K\eta K^\dagger + \sum_i L_i \eta L_i^\dagger = \rho' + \rho_{\mathrm{rem}}$. Since $\eta \geq 0$ and $\sum_i L_i(\cdot)L_i^\dagger$ is completely positive, $\rho_{\mathrm{rem}} \geq 0$, giving the operator inequality $\mathcal{N}(\eta) \geq \rho'$. Conjugate by $\sqrt{\sigma}$: $\sqrt{\sigma}\,\mathcal{N}(\eta)\,\sqrt{\sigma} \geq \sqrt{\sigma}\,\rho'\,\sqrt{\sigma}$. By the Lowner-Heinz theorem ($f(x) = \sqrt{x}$ is operator monotone), $\sqrt{\sqrt{\sigma}\,\mathcal{N}(\eta)\,\sqrt{\sigma}} \geq \sqrt{\sqrt{\sigma}\,\rho'\,\sqrt{\sigma}}$. Taking traces (a positive linear functional) gives $F(\mathcal{N}(\eta), \sigma) \geq F(\rho', \sigma)$.

**Role:** Used in [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] Step 2 to reduce from the full channel $\widetilde{\mathcal{C}}_{\mu \to \nu}$ to the single highest-weight Kraus branch $\mathcal{K}_\omega$, which is much easier to analyze because $|\omega\rangle$ is annihilated by raising operators.

---

## Dimension Ratio (Lemma 10)

**Label:** `lem:dim_ratio`
**Source:** Article line ~1776 (stated), ~2831 (proved)

**Statement:** For $\nu = \mu + \omega$ in the scaling regime $g_\mu = \Theta(n)$, $\mu_r = \Theta(n)$, $|\omega| = o(n)$:

$$\frac{d_\mu}{d_\nu} = 1 - O\left(\frac{|\omega|}{n}\right) = 1 - O\left(\frac{d(\mu,\nu)}{n}\right)$$

**Proof detail:** By the Weyl dimension formula, $d_\nu/d_\mu = \prod_{i < j} (1 + y_{ij})$ where $y_{ij} = (\omega_i - \omega_j)/(\mu_i - \mu_j + j - i)$. Since $\omega$ is dominant, $y_{ij} \geq 0$. The denominators are bounded below: for $1 \leq i < j \leq r$, $\mu_i - \mu_j + j - i \geq g_\mu = \Theta(n)$; for $1 \leq i \leq r < j \leq d$, $\mu_i + j - i \geq \mu_r = \Theta(n)$; for $r < i < j \leq d$, $\omega_i = \omega_j = 0$ so $y_{ij} = 0$. Thus $0 \leq y_{ij} \leq C|\omega|/n$ uniformly. Since there are $O_d(1)$ factors and $\log(1 + y) = y + O(y^2)$, summing gives $\log(d_\nu/d_\mu) = \sum_{i<j} y_{ij} + O(|\omega|^2/n^2) = O(|\omega|/n)$.

**Role:** Ensures the normalization prefactor $\sqrt{d_\mu/d_\nu}$ in the block fidelity formula is close to 1, contributing only an $O(d(\mu,\nu)/n)$ correction.

---

## Asymptotic Weyl Dimension (Lemma 11)

**Label:** `lem:weyl_asymptotic`
**Source:** Article line ~521

**Statement:** For a partition $\lambda$ with $\lambda_i = nx_i + O(\sqrt{n}\Delta_n)$ for $1 \leq i \leq r$ and $\lambda_i = 0$ for $i > r$ (with $\Delta_n = o(\sqrt{n})$):

$$\log \dim \mathcal{H}_\lambda = \frac{r(2d-r-1)}{2}\log n + \sum_{i < j \leq r} \log(x_i - x_j) + (d-r)\sum_i \log x_i - \sum_{k=d-r}^{d-1} \log k! + O\left(\frac{\Delta_n}{\sqrt{n}}\right)$$

**Proof detail:** The exact Weyl dimension formula is $\dim \mathcal{H}_\lambda = \prod_{1 \leq i < j \leq d} (\lambda_i - \lambda_j + j - i)/(j - i)$. Split the product into three blocks based on the rank $r$:
1. **Nonzero vs. nonzero** ($1 \leq i < j \leq r$): $\lambda_i - \lambda_j = n(x_i - x_j)(1 + O(\Delta_n/\sqrt{n}))$, contributing $n^{r(r-1)/2} \prod_{i<j\leq r}(x_i - x_j)$ times a $(1+O(\Delta_n/\sqrt{n}))$ correction.
2. **Nonzero vs. zero** ($1 \leq i \leq r < j \leq d$): $\lambda_i + j - i = nx_i(1 + O(\Delta_n/\sqrt{n}))$, contributing $n^{r(d-r)} \prod_i x_i^{d-r}$.
3. **Zero vs. zero** ($r < i < j \leq d$): exactly $j - i$, giving $\prod_{k=1}^{d-r-1} k!$.

Dividing by the denominator $\prod_{k=1}^{d-1} k!$ leaves $1/\prod_{k=d-r}^{d-1} k!$. The total power of $n$ is $r(r-1)/2 + r(d-r) = r(2d-r-1)/2$. Taking logarithms, the multiplicative $(1 + O(\Delta_n/\sqrt{n}))$ factor becomes an additive $O(\Delta_n/\sqrt{n})$.

**Role:** This is the key formula connecting irrep dimensions to the QMDL rate. Used in both [[results/achievability|Achievability (State Compression)]] (to compute $\log \dim \mathcal{H}_{\Lambda^*}$) and [[results/converse|Converse (State Compression)]] (to evaluate $\log \dim \mathcal{H}_{\lambda^{(n)}}$ for typical $\lambda^{(n)}$).

---

## Sanov's Theorem / Tail Probability (Lemma 12)

**Label:** `lem:tail_prob`
**Source:** Article line ~617; Notes line ~1136

**Statement:**

$$\Pr\left[\lambda : d(\lambda/n, p) > x\right] \leq (n+1)^{r(r+1)/2} e^{-2nx^2}$$

where $d(\lambda/n, p) = \frac{1}{2}\sum_i |\lambda_i/n - x_i|$ is the total variation distance between the empirical type $\lambda/n$ and the true spectrum $p$.

**Proof detail:** This is a standard exponential concentration bound for the empirical type under i.i.d. sampling. The polynomial prefactor $(n+1)^{r(r+1)/2}$ is a union bound over the number of distinct types (partitions of $n$ with at most $d$ parts), and the exponential $e^{-2nx^2}$ comes from the relative entropy bound in Sanov's theorem: $q_{\lambda,n} \leq e^{-nD(\lambda/n \| p)}$ where $D$ is the KL divergence, combined with Pinsker's inequality $D(q\|p) \geq 2 d_{\mathrm{TV}}(q,p)^2$.

**Role:** Proves that the Young diagram $\lambda$ concentrates near $np$ in the typical set, justifying the restriction to $\mathcal{T}_{p,n}$ in both the achievability and converse proofs. The atypical tail is exponentially small.

---

## Commutativity (Proposition 3)

**Label:** `prop:commutativity` (Article), `lem:commutativity` (Notes)
**Source:** Article line ~421 (stated), ~2190 (proved); Notes line ~862

**Statement:** For any $\mathrm{U}(d)$-covariant channel $\mathcal{C}_{\mu \to \nu}$:

$$[\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu] = 0$$

**Proof detail:** Work in the eigenbasis of $\rho$ where $\rho = \Lambda$ is diagonal. Both $\rho_\mu \propto \pi_\mu(\Lambda)$ and $\rho_\nu \propto \pi_\nu(\Lambda)$ are then images of a diagonal matrix. The maximal torus $T \subset \mathrm{U}(d)$ of diagonal unitaries commutes with $\Lambda$, so $[\rho_\mu, U_\mu(t)] = 0$ for all $t \in T$. By $\mathrm{U}(d)$-covariance, $\mathcal{C}_{\mu \to \nu}(U_\mu(t)\rho_\mu U_\mu(t)^{-1}) = U_\nu(t)\mathcal{C}_{\mu \to \nu}(\rho_\mu)U_\nu(t)^{-1}$. Since $\rho_\mu$ commutes with $U_\mu(t)$, the left side is just $\mathcal{C}_{\mu \to \nu}(\rho_\mu)$, so $[\mathcal{C}_{\mu \to \nu}(\rho_\mu), U_\nu(t)] = 0$ for all $t \in T$. Now $\mathcal{H}_\nu$ decomposes into weight spaces $W_\nu(\delta)$ which the torus distinguishes via unique phase characters, so $\mathcal{C}_{\mu \to \nu}(\rho_\mu)$ must be block-diagonal in the weight basis. Since $\rho_\nu$ acts as a scalar on each weight space, the two operators commute.

**Role:** Simplifies the fidelity computation to a classical (diagonal) problem -- both $\mathcal{C}_{\mu \to \nu}(\rho_\mu)$ and $\rho_\nu$ are diagonal in the weight basis, so fidelity reduces to a sum over weight blocks.

---

## Reverse Cloner (Proposition 2)

**Label:** `prop:reverse`
**Source:** Article line ~392 (stated), ~2027 (proved)

**Statement:** The Petz recovery map of $\mathcal{C}_{\mu \to \nu}$ with respect to $\sigma_\mu = I/d_\mu$ equals the reverse cloning map:

$$\mathcal{C}_{\nu \to \mu}(X) = \frac{d_\nu}{d_\mu} \mathcal{C}_{\mu \to \nu}^\dagger(X)$$

**Proof detail:** First, the cloning map sends maximally mixed to maximally mixed: by covariance and Schur's lemma, $\mathcal{C}_{\mu \to \nu}(\sigma_\mu) = \sigma_\nu$. So the Petz map simplifies to $\mathcal{R}(X) = \sigma_\mu^{1/2} \mathcal{C}_{\mu \to \nu}^\dagger(\sigma_\nu^{-1/2} X \sigma_\nu^{-1/2}) \sigma_\mu^{1/2} = (d_\nu/d_\mu) \mathcal{C}_{\mu \to \nu}^\dagger(X)$.

To verify this equals $\mathcal{C}_{\nu \to \mu}$: the Kraus operators $\{K_a\}$ of $\mathcal{C}_{\mu \to \nu}$ span a space $\mathsf{K}_\omega \subset \mathrm{Hom}(\mathcal{H}_\mu, \mathcal{H}_\nu)$ carrying the irrep $\omega$ under $K \mapsto U_\nu(g) K U_\mu(g)^\dagger$. The Hilbert-Schmidt adjoint $K \mapsto K^\dagger$ gives an antiunitary intertwiner, so $\{K_a^\dagger\}$ spans a space carrying the dual irrep $\omega^* = (-w_0\omega) = (\mu - \nu)^+$, which is exactly the PRV component for the reversed pair. The Choi operator of $(d_\nu/d_\omega)\sum_a K_a^\dagger (\cdot) K_a$ is $(d_\nu/d_{\omega^*})\Pi_{\omega^*}$ -- the Choi operator of $\mathcal{C}_{\nu \to \mu}$.

**Role:** Justifies using the reverse cloner for decompression: in the Stinespring picture, $\mathcal{C}_{\nu \to \mu}(X) = \mathrm{Tr}_\omega(VXV^\dagger)$ is simply a partial trace, which enables the elegant reverse-direction argument in [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] Step 9.

---

## Irreducible Orbit Sector Compression (Proposition 4)

**Label:** `prop:orbit_sector_converse`
**Source:** Article line ~666

**Statement:** For any sequence of partitions $\{\lambda^{(n)}\}$, if a sector code achieves vanishing Haar-average error:

$$|M_n| \geq \log \dim \mathcal{H}_\lambda + o(1)$$

**Proof detail:** The proof establishes that the orbit ensemble generates the full operator algebra $\mathfrak{A}_\lambda = \mathcal{B}(\mathcal{H}_\lambda)$ in three steps:

1. **Lagrange interpolation:** Since the spectrum $x$ has distinct entries, the eigenvalues of $\rho_\lambda$ are distinct (the highest-weight eigenvalue $x^\lambda/s_\lambda(x)$ is strictly largest). The rank-one projector onto the highest-weight vector is a polynomial in $\rho_\lambda$: $|v_\lambda\rangle\langle v_\lambda| = \prod_{j \neq 1} (\rho_\lambda - x_j I)/(x_1 - x_j)$. Therefore $|v_\lambda\rangle\langle v_\lambda| \in \mathfrak{A}_\lambda$, and by covariance, $U_\lambda(g)|v_\lambda\rangle\langle v_\lambda|U_\lambda(g)^\dagger \in \mathfrak{A}_\lambda$ for all $g$.

2. **Orbit spans $\mathcal{H}_\lambda$:** If $X$ commutes with every $|u_g\rangle\langle u_g|$ (where $|u_g\rangle = U_\lambda(g)|v_\lambda\rangle$), then $X|u_g\rangle = a(g)|u_g\rangle$ for some continuous $a: \mathrm{U}(d) \to \mathrm{spec}(X)$ (a finite set). Since $\mathrm{U}(d)$ is connected, $a$ must be constant: $a(g) \equiv a$. The orbit $\{|u_g\rangle\}$ spans all of $\mathcal{H}_\lambda$ (it is a nonzero invariant subspace of the irrep), so $X = aI$.

3. **Bicommutant theorem:** This proves the commutant $\mathfrak{A}_\lambda' = \mathbb{C} \cdot I$, so by the finite-dimensional bicommutant theorem, $\mathfrak{A}_\lambda = \mathcal{B}(\mathcal{H}_\lambda)$.

Finally, the [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]] for blind compression of mixed-state ensembles says the asymptotically necessary quantum memory equals $\log \dim$ of the nonredundant quantum factor determined by the $C^*$-algebra of the ensemble. Since that algebra is the full $\mathcal{B}(\mathcal{H}_\lambda)$, the entire irrep space is nonredundant, giving $|M_n| \geq \log \dim \mathcal{H}_\lambda + o(1)$.

**Role:** The key ingredient in [[results/converse|Converse (State Compression)]] -- once we identify a typical sector with vanishing error, this proposition gives the per-sector memory lower bound.

## External References

- [Davis and Kahan, "The rotation of eigenvectors by a perturbation. III" (1970)](https://doi.org/10.1007/BF02757689)
- [Koashi and Imoto, "Compressibility of quantum mixed-state signals" (2001)](https://arxiv.org/abs/quant-ph/0101144)
