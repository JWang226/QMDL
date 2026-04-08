# Cloning Fidelity (Theorem 1)

**Label:** `thm:main` (Article), `prop:main` (Notes)
**Source:** Article line ~412 (stated), ~950 (restated), ~1109 (proved); Notes line ~454

## Statement

Let $\rho$ be a density matrix of rank $r$ with strictly non-degenerate positive eigenvalues $x_1 > \cdots > x_r > 0$. Let $\mu, \nu$ be $\mathrm{GL}(d)$ highest weights with $|\mu|, |\nu| = \Theta(n)$, $(\nu - \mu)$ dominant, and $d(\mu, \nu) = \sum_i |\mu_i - \nu_i|$.

Then for any $\varepsilon > 0$:

$$F(\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu) \geq 1 - O\left(\frac{d(\mu, \nu)}{n^{1-\varepsilon}}\right)$$

and similarly:

$$F(\mathcal{C}_{\nu \to \mu}(\rho_\nu), \rho_\mu) \geq 1 - O\left(\frac{d(\mu, \nu)}{n^{1-\varepsilon}}\right)$$

## Intuition

The [[concepts/generalized-cloning-map|Generalized Cloning Map]] approximately preserves the state when mapping between nearby irreps. "Nearby" means $d(\mu, \nu) \ll n$: the Young diagrams differ by much less than their total size. The fidelity approaches 1 polynomially fast in $n$.

The deep reason this works is that for large $n$, the tensor product $\mathcal{H}_\mu \otimes \mathcal{H}_\omega$ (where $\omega = \nu - \mu$) is "mostly $\mathcal{H}_\nu$" -- the Casimir operator forces the $\nu$-component to be energetically dominant, and a perturbation theory argument shows that weight spaces align between $\mathcal{H}_\nu$ and the embedded $\mathcal{H}_\mu \otimes |\omega\rangle$. The proof carefully decomposes the fidelity into a quantum part (subspace alignment) and a classical part (probability matching), bounding each separately.

## Proof Sketch

**Main idea:** Embed $\mathcal{H}_\nu$ into $\mathcal{H}_\mu \otimes \mathcal{H}_\omega$ via the PRV isometry, then isolate the highest-weight Kraus branch (where $E_\alpha^{(\omega)}|\omega\rangle = 0$ kills half the perturbation). The fidelity splits into a **classical part** (weight probability overlap, exponentially close to 1 via a determinantal identity) and a **quantum part** (subspace alignment, controlled by Davis-Kahan perturbation of the Casimir with spectral gap $\Theta(n)$). Truncating deep weights at depth $O(n^\varepsilon)$ and using dimension stability of the Weyl formula gives the final $1 - O(d(\mu,\nu)/n^{1-\varepsilon})$ bound.

---

### Extended Proof

The proof proceeds in nine steps. We set $\omega := \nu - \mu$ (dominant by hypothesis), so $d(\mu,\nu) = |\omega|$.

### Step 1: Stinespring Embedding

Rather than working directly with the intrinsic channel $\mathcal{C}_{\mu \to \nu}: \mathcal{B}(\mathcal{H}_\mu) \to \mathcal{B}(\mathcal{H}_\nu)$, embed everything into the product space $\mathcal{H}_\mu \otimes \mathcal{H}_\omega$ using the intertwining isometry $V: \mathcal{H}_\nu \hookrightarrow \mathcal{H}_\mu \otimes \mathcal{H}_\omega$ (the PRV embedding). The embedded channel becomes:

$$\widetilde{\mathcal{C}}_{\mu \to \nu}(X) = V \mathcal{C}_{\mu \to \nu}(X) V^\dagger = \frac{d_\mu}{d_\nu} P_\nu (X \otimes \mathrm{id}_\omega) P_\nu$$

where $P_\nu = V V^\dagger$ is the projector onto the $\nu$-isotypic component inside $\mathcal{H}_\mu \otimes \mathcal{H}_\omega$. This is advantageous because fidelity is isometrically invariant, so $F(\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu) = F(\widetilde{\mathcal{C}}_{\mu \to \nu}(\rho_\mu), \widetilde{\rho}_\nu)$, and the product space structure lets us use Casimir perturbation theory.

### Step 2: Highest-Weight Kraus Operator and Monotonicity

Choose an orthonormal basis $\{|a\rangle\}$ of $\mathcal{H}_\omega$ containing the highest-weight vector $|\omega\rangle$. The embedded channel decomposes into Kraus branches:

$$\widetilde{\mathcal{C}}_{\mu \to \nu}(X) = \sum_a \mathcal{K}_a(X), \qquad \mathcal{K}_a(X) = \frac{d_\mu}{d_\nu} P_\nu (X \otimes |a\rangle\langle a|) P_\nu$$

The highest-weight branch $\mathcal{K}_\omega$ corresponds to $|a\rangle = |\omega\rangle$. By the [[results/remaining-lemmas|Monotonicity (Lemma 5)]], which says that discarding Kraus branches can only decrease fidelity (since $\rho' = K\eta K^\dagger \leq \mathcal{N}(\eta)$ and the Lowner-Heinz theorem gives $F(\rho', \sigma) \leq F(\rho, \sigma)$), we get:

$$F(\widetilde{\mathcal{C}}_{\mu \to \nu}(\rho_\mu), \widetilde{\rho}_\nu) \geq F(\mathcal{K}_\omega(\rho_\mu), \widetilde{\rho}_\nu)$$

This lower bound is the key reduction: we only need to analyze the single Kraus branch where the $\omega$-register is pinned to the highest weight.

### Step 3: Weight Block Decomposition

Since $\mathcal{K}_\omega(\Pi_{\mu - \delta})$ is supported on the total-weight sector $\nu - \delta$ (because $|\omega\rangle$ has weight $\omega$ and $\Pi_{\mu - \delta}$ has weight $\mu - \delta$, so the total weight is $\mu - \delta + \omega = \nu - \delta$), the fidelity decomposes blockwise over positive root sums $\delta \in Q_+$:

$$F(\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu) \geq \sum_{\delta \in Q_+} \sqrt{p_\mu(\delta) \, p_\nu(\delta)} \cdot F_{\mathrm{block}}(\delta)$$

This cleanly separates into:
- **Classical part:** The Bhattacharyya coefficient $\sum_\delta \sqrt{p_\mu(\delta) \, p_\nu(\delta)}$, which measures how well the weight probability distributions match.
- **Quantum part:** The block fidelity $F_{\mathrm{block}}(\delta)$, which measures the alignment of weight subspaces within each sector.

### Step 4: Quantum Part -- Davis-Kahan Perturbation of the Casimir

The block fidelity $F_{\mathrm{block}}(\delta)$ compares two projectors inside the total-weight slice $W_{\nu - \delta} \subset \mathcal{H}_\mu \otimes \mathcal{H}_\omega$:
- $\widetilde{\Pi}_{\nu - \delta} = Q_{\nu-\delta} P_\nu$: the exact coupled projector (weight $\nu - \delta$ subspace of $\mathcal{H}_\nu$)
- $\Pi_{\mu-\delta}^{(\omega)} = \Pi_{\mu-\delta} \otimes |\omega\rangle\langle\omega|$: the uncoupled product projector

The [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]] bounds their distance. The idea: view the total quadratic Casimir $C_2(\mu \otimes \omega)$ restricted to $W_{\nu-\delta}$ as $H = H_0 + V$, where $H_0$ is the diagonal Cartan part (eigenvalue $\lambda_0 = C_2(\mu) + C_2(\omega) + 2(\mu - \delta, \omega)$ on the uncoupled subspace) and $V$ contains the root-exchange terms $E_{-\alpha}^{(\mu)} \otimes E_\alpha^{(\omega)} + E_\alpha^{(\mu)} \otimes E_{-\alpha}^{(\omega)}$.

**Key trick:** On $P_0 = \Pi_{\mu-\delta}^{(\omega)}$, the raising operators $E_\alpha^{(\omega)}|\omega\rangle = 0$ kill the highest-weight vector, so only half the perturbation survives: $VP_0 = 2 Q_{\nu-\delta} \sum_{\alpha > 0} E_\alpha^{(\mu)} \otimes E_{-\alpha}^{(\omega)} P_0$.

This gives the tighter bound $\|VP_0\| = O(\sqrt{n \, |\delta| \, \|\omega\|})$ instead of the full norm $\|V\| = O(|\delta| \sqrt{n \|\omega\|})$. The spectral gap is $\Delta = 2 g_\mu |\eta| - O(|\delta||\eta|) - O(\|\omega\||\eta|) = \Theta(n)$ (using $g_\mu = \min_i(\mu_i - \mu_{i+1}) = \Theta(n)$). Applying the [[results/remaining-lemmas|Davis-Kahan Theorem (Lemma 6)]]:

$$\|\widetilde{\Pi}_{\nu-\delta} - \Pi_{\mu-\delta}^{(\omega)}\| \leq \frac{\|VP_0\|}{\Delta - \|V\|} = \frac{O(\sqrt{n \, |\delta| \, \|\omega\|})}{\Omega(n)} = O\left(\sqrt{\frac{|\delta| \, \|\omega\|}{n}}\right)$$

By [[results/remaining-lemmas|Principal Angles (Lemma 4)]], $F_{\mathrm{block}}(\delta) = \sqrt{d_\mu / d_\nu} \sum_{i=1}^{m(\delta)} \cos\theta_i$ where $\theta_i$ are the principal angles. Using $\cos\theta \geq 1 - \sin^2\theta$ and $\sin\theta_{\max} = O(\sqrt{|\delta|\|\omega\|/n})$:

$$F_{\mathrm{block}}(\delta) \geq \sqrt{\frac{d_\mu}{d_\nu}} \, m(\delta) \left(1 - O\left(\frac{|\delta| \, \|\omega\|}{n}\right)\right)$$

where $m(\delta) = K_{\mu, \mu-\delta} = K_{\nu, \nu-\delta}$ by the [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] (equality holds because $|\delta| \leq g_\mu$ in the regime of interest).

### Step 5: Classical Part -- Determinantal Probability Ratio

The probability ratio $p_\nu(\delta)/p_\mu(\delta) = x^\omega s_\mu(x) / s_{\mu+\omega}(x)$ is independent of $\delta$ -- a crucial simplification. The [[results/probability-ratio|Probability Ratio (Lemma 9)]] shows this ratio $Z(x)$ satisfies:

$$1 \geq Z(x) \geq 1 - O(e^{-(g_\mu + 1)\xi})$$

where $\xi = \min_i(\ln x_i - \ln x_{i+1})$ is the logarithmic spectral gap. Since $g_\mu = \Theta(n)$, this is exponentially close to 1 -- the classical distributions are essentially identical. The Bhattacharyya coefficient $\sum_\delta \sqrt{p_\mu(\delta) p_\nu(\delta)} = \sqrt{Z(x)} \sum_\delta p_\mu(\delta) m(\delta)$ thus introduces only an exponentially small correction.

### Step 6: Tail Truncation

The perturbation bound from Step 4 requires $|\delta|^2 \|\omega\| \ll n$, so we truncate the sum at a cutoff $T = O(n^\varepsilon)$ for arbitrarily small $\varepsilon > 0$. The [[results/tail-mass|Tail Mass (Lemma 8)]] bounds the omitted contribution:

$$\varepsilon_\mu(T) = \sum_{|\delta| > T} p_\mu(\delta) \, m_\mu(\delta) = O(T^\kappa \, \mathfrak{p}^T)$$

where $\kappa = r(r-1)/2 - 1$ and $\mathfrak{p} = \max_i(x_{i+1}/x_i) < 1$. When $T = O(n^\varepsilon)$, this is $O(n^{\varepsilon \kappa} \mathfrak{p}^{n^\varepsilon})$, which is superpolynomially small -- far smaller than the polynomial error from the perturbation bound. The total state is normalized: $\sum_\delta p_\mu(\delta) m(\delta) = \mathrm{Tr}(\rho_\mu) = 1$, so the truncated sum captures essentially all the mass.

### Step 7: Dimension Stability

The [[results/remaining-lemmas|Dimension Ratio (Lemma 10)]] gives the prefactor: using the Weyl dimension formula and the scaling $g_\mu = \Theta(n)$, $\mu_r = \Theta(n)$, $|\omega| = o(n)$:

$$\frac{d_\mu}{d_\nu} = \prod_{i < j} \frac{\mu_i - \mu_j + j - i}{\mu_i + \omega_i - \mu_j - \omega_j + j - i} = 1 - O\left(\frac{|\omega|}{n}\right)$$

Each factor in the Weyl formula changes by a multiplicative $1 + y_{ij}$ where $y_{ij} = (\omega_i - \omega_j)/(\mu_i - \mu_j + j - i) = O(|\omega|/n)$, and there are $O(1)$ such factors (since $d$ is fixed). This ensures $\sqrt{d_\mu/d_\nu} = 1 - O(d(\mu,\nu)/n)$.

### Step 8: Combining All Estimates (Forward Direction)

Setting the cutoff $T = O(n^\varepsilon)$ and using $\|\omega\| \leq |\omega| = d(\mu,\nu)$, the forward fidelity satisfies:

$$F(\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu) \geq \underbrace{\left(1 - O\left(\frac{d(\mu,\nu)}{n^{1-\varepsilon}}\right)\right)}_{\text{quantum (Step 4)}} \cdot \underbrace{\left(1 - O(e^{-\Theta(n)})\right)}_{\text{classical (Step 5)}} \cdot \underbrace{(1 - O(n^{\varepsilon\kappa} \mathfrak{p}^{n^\varepsilon}})}_{\text{tail (Step 6)}} \cdot \underbrace{\left(1 - O\left(\frac{d(\mu,\nu)}{n}\right)\right)}_{\text{dimension (Step 7)}}$$

The classical and tail terms are superpolynomially small, and the dimension term is dominated by the quantum term. The bottleneck is the quantum perturbation:

$$F(\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu) \geq 1 - O\left(\frac{d(\mu,\nu)}{n^{1-\varepsilon}}\right)$$

### Step 9: Reverse Direction via Partial Trace Monotonicity

For the reverse channel $\mathcal{C}_{\nu \to \mu}$, the argument is structurally different. The reverse cloner (by [[results/remaining-lemmas|Reverse Cloner (Prop 2)]]) satisfies $\mathcal{C}_{\nu \to \mu}(X) = \mathrm{Tr}_\omega(V X V^\dagger)$, i.e., it is the partial trace of the Stinespring embedding.

Define $\rho_\mu^{(\omega)} = \rho_\mu \otimes |\omega\rangle\langle\omega|$. Then $\mathrm{Tr}_\omega(\widetilde{\rho}_\nu) = \mathcal{C}_{\nu \to \mu}(\rho_\nu)$ and $\mathrm{Tr}_\omega(\rho_\mu^{(\omega)}) = \rho_\mu$. By monotonicity of fidelity under partial trace:

$$F(\mathcal{C}_{\nu \to \mu}(\rho_\nu), \rho_\mu) = F(\mathrm{Tr}_\omega(\widetilde{\rho}_\nu), \mathrm{Tr}_\omega(\rho_\mu^{(\omega)})) \geq F(\widetilde{\rho}_\nu, \rho_\mu^{(\omega)})$$

The right side decomposes into the same weight-block structure as before:

$$F(\widetilde{\rho}_\nu, \rho_\mu^{(\omega)}) = \sum_{\delta \in Q_+} \sqrt{p_\mu(\delta) p_\nu(\delta)} \cdot F(\widetilde{\Pi}_{\nu-\delta}, \Pi_{\mu-\delta}^{(\omega)})$$

The block fidelities are the same principal angle sums as in Step 4, but now without the $\sqrt{d_\mu/d_\nu}$ prefactor (because we are comparing projectors directly, not through the channel). Applying the same perturbation, probability ratio, and tail estimates:

$$F(\mathcal{C}_{\nu \to \mu}(\rho_\nu), \rho_\mu) \geq 1 - O\left(\frac{d(\mu,\nu)}{n^{1-\varepsilon}}\right)$$

## Dependencies

- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- the channel being analyzed
- [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]] -- bounds principal angles via Casimir perturbation (Step 4)
- [[results/remaining-lemmas|Davis-Kahan Theorem (Lemma 6)]] -- perturbation of eigenspaces
- [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] -- ensures weight space dimensions match ($K_{\mu,\mu-\delta} = K_{\nu,\nu-\delta}$ for $|\delta| \leq g_\mu$)
- [[results/remaining-lemmas|Principal Angles (Lemma 4)]] -- connects fidelity to geometric angles between subspaces
- [[results/tail-mass|Tail Mass (Lemma 8)]] -- controls deep weight contributions (Step 6)
- [[results/probability-ratio|Probability Ratio (Lemma 9)]] -- bounds classical distribution mismatch (Step 5)
- [[results/remaining-lemmas|Dimension Ratio (Lemma 10)]] -- dimension stability (Step 7)
- [[results/remaining-lemmas|Monotonicity (Lemma 5)]] -- channel monotonicity of fidelity (Step 2)
- [[results/remaining-lemmas|Commutativity (Prop 3)]] -- output commutes with target
- [[results/remaining-lemmas|Reverse Cloner (Prop 2)]] -- identifies reverse channel as partial trace (Step 9)

## Used By

- [[results/achievability|Achievability (State Compression)]] -- main application

## Key Equations

The block fidelity formula after all substitutions:

$$F_{\mathrm{block}}(\delta) = \sqrt{\frac{d_\mu}{d_\nu}} \sum_{i=1}^{m(\delta)} \cos\theta_i \geq \sqrt{\frac{d_\mu}{d_\nu}} \, m(\delta) \left(1 - O\left(\frac{|\delta|\|\omega\|}{n}\right)\right)$$

The final combined bound before simplification:

$$F \geq \left(1 - O\left(\frac{d(\mu,\nu)}{n^{1-\varepsilon}}\right)\right) \sum_{|\delta| \leq T} p_\mu(\delta) \, m(\delta) \, \sqrt{Z(x)} \geq 1 - O\left(\frac{d(\mu,\nu)}{n^{1-\varepsilon}}\right)$$

## External References

- [Werner, "Optimal cloning of pure states" (1998)](https://doi.org/10.1103/PhysRevA.58.1827)
- [Davis and Kahan, "The rotation of eigenvectors by a perturbation. III" (1970)](https://doi.org/10.1137/0707001)
