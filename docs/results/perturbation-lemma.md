# Perturbation Lemma (Lemma 7)

**Label:** `lem:perturbation` (Article)
**Source:** Article line ~1230 (stated), ~1264 (proved); Notes line ~665

## Statement

Let $\nu = \mu + \omega$ with $\mu, \omega$ dominant. Let $P_\nu$ project onto $\mathcal{H}_\nu \subset \mathcal{H}_\mu \otimes \mathcal{H}_\omega$, and let $P_\mu^{(\omega)} = \mathrm{id}_\mu \otimes |\omega\rangle\langle\omega|$. For a positive root sum $\delta \in Q_+$, define the restricted projectors $\widetilde{\Pi}_{\nu-\delta} = Q_{\nu-\delta} P_\nu$ and $\Pi_{\mu-\delta}^{(\omega)} = Q_{\nu-\delta} P_\mu^{(\omega)}$ (both commute with $Q_{\nu-\delta}$ since they respect the total Cartan action). Then:

$$\|\widetilde{\Pi}_{\nu-\delta} - \Pi_{\mu-\delta}^{(\omega)}\| = O\left(\sqrt{\frac{|\delta| \, \|\omega\|}{n}}\right)$$

under the scaling regime $|\mu| = \Theta(n)$, $g_\mu = \Theta(n)$, $|\delta|^2 \|\omega\| \ll n$, where $\|\omega\| = \omega_1 - \omega_d$ is the width of $\omega$.

## Intuition

The weight spaces of $\mathcal{H}_\nu$ are "close" to the product weight spaces $\mathcal{H}_\mu \otimes |\omega\rangle$ viewed inside $\mathcal{H}_\mu \otimes \mathcal{H}_\omega$. Physically, tensoring a large irrep ($\mu$ of size $\Theta(n)$) with a small one ($\omega$) barely changes the weight space geometry -- the Clebsch-Gordan coupling is a small perturbation of the uncoupled product. The proof makes this precise using the Casimir operator as a Hamiltonian and applying the Davis-Kahan theorem to its spectral projectors.

## Proof Sketch

**Main idea:** Treat the total Casimir restricted to a fixed weight slice as a perturbed Hamiltonian $H = H_0 + V$. The uncoupled product subspace $\Pi_{\mu-\delta} \otimes |\omega\rangle$ is an eigenspace of $H_0$ with spectral gap $\Delta = \Theta(n)$ (from the edge gap $g_\mu$). The key trick: $E_\alpha^{(\omega)}|\omega\rangle = 0$ annihilates half the perturbation on this subspace, giving $\|VP_0\| = O(\sqrt{n|\delta|\|\omega\|})$ instead of the full $\|V\| = O(|\delta|\sqrt{n\|\omega\|})$. Davis-Kahan then yields $\|P - P_0\| \leq \|VP_0\|/\Delta = O(\sqrt{|\delta|\|\omega\|/n})$.

---

### Extended Proof

### Setup: Casimir as a Hamiltonian

Work on the fixed total-weight slice $W_{\nu-\delta} \subset \mathcal{H}_\mu \otimes \mathcal{H}_\omega$. The total quadratic Casimir restricted to this slice is:

$$H = Q_{\nu-\delta} \, C_2(\mu \otimes \omega) \, Q_{\nu-\delta}$$

Split as $H = H_0 + V$ where:

$$H_0 = Q \left(C_2(\mu) \otimes \mathrm{id}_\omega + \mathrm{id}_\mu \otimes C_2(\omega) + 2\sum_{i=1}^d H_i^{(\mu)} \otimes H_i^{(\omega)}\right) Q$$

is the diagonal Cartan part, and:

$$V = Q \left(2\sum_{\alpha > 0} \left(E_{-\alpha}^{(\mu)} \otimes E_\alpha^{(\omega)} + E_\alpha^{(\mu)} \otimes E_{-\alpha}^{(\omega)}\right)\right) Q$$

contains the root-exchange (off-diagonal) terms.

### Step 1: Identify the Unperturbed Eigenspace

The projector $P_0 = \Pi_{\mu-\delta}^{(\omega)} = \Pi_{\mu-\delta} \otimes |\omega\rangle\langle\omega|$ is an eigenspace of $H_0$ with eigenvalue:

$$\lambda_0 = C_2(\mu) + C_2(\omega) + 2(\mu - \delta, \omega)$$

This is because $|\omega\rangle$ has weight $\omega$, so fixing total weight $\nu - \delta$ forces the $\mu$-register to weight $\mu - \delta$, and the Cartan interaction term $2\sum_i H_i^{(\mu)} \otimes H_i^{(\omega)}$ evaluates to $2(\mu-\delta, \omega)$ on this product subspace.

### Step 2: Spectral Gap is $\Theta(n)$

Any vector in $W_{\nu-\delta}$ orthogonal to $P_0$ must have the $\omega$-register at some lower weight $\omega - \eta$ with $\eta \in Q_+$, $\eta \neq 0$ (and correspondingly the $\mu$-register at weight $\mu - \delta + \eta$). The eigenvalue of $H_0$ on such a subspace is $\lambda_1(\eta) = C_2(\mu) + C_2(\omega) + 2(\mu - \delta + \eta, \omega - \eta)$.

The gap $\lambda_0 - \lambda_1(\eta)$ is computed by expanding:

$$\lambda_0 - \lambda_1(\eta) = 2(\mu, \eta) - 2(\delta, \eta) - 2(\omega, \eta) + 2(\eta, \eta)$$

Bounding each term using the simple root decomposition $\eta = \sum_k c_k \alpha_k$:
- $(\mu, \eta) = \sum_k c_k(\mu_k - \mu_{k+1}) \geq g_\mu |\eta|$ (each $\mu_k - \mu_{k+1} \geq g_\mu$)
- $|(\delta, \eta)| \leq 2|\delta| \, |\eta|$ (using $|(\alpha_i, \alpha_k)| \leq 2$ in type $A$)
- $(\omega, \eta) = \sum_k c_k(\omega_k - \omega_{k+1}) \leq \|\omega\| \, |\eta|$
- $(\eta, \eta) \geq 0$

Therefore:
$$\lambda_0 - \lambda_1(\eta) \geq |\eta|(2g_\mu - 4|\delta| - 2\|\omega\|)$$

Since $g_\mu = \Theta(n)$ and $|\delta|, \|\omega\| = o(n)$ (implied by $|\delta|^2\|\omega\| \ll n$), the bracket is $\Theta(n)$, giving a spectral gap $\Delta = \Omega(n)$.

### Step 3: The Perturbed Projector is $\widetilde{\Pi}_{\nu-\delta}$

The perturbed Hamiltonian $H = H_0 + V$ is the total Casimir restricted to the slice, so its eigenspaces are exactly $Q_{\nu-\delta} P_\lambda$ for irreps $\lambda \subset \mu \otimes \omega$. We need to verify that $Q_{\nu-\delta} P_\nu$ is the spectral projector near $\lambda_0$.

The eigenvalue of $H$ on $Q_{\nu-\delta} P_\nu$ is $C_2(\nu)$, and $|\lambda_0 - C_2(\nu)| = 2|(\delta, \omega)| \leq 2|\delta| \|\omega\| = o(n)$, so it lies within the spectral gap. Any competing irrep $\nu - \gamma$ (with $\gamma \preceq \delta$, $\gamma \neq 0$) has Casimir $C_2(\nu) - C_2(\nu - \gamma) \geq 2g_\mu|\gamma| - O(|\gamma|^2) = \Omega(n)$, so it lies far below. This confirms $P = \widetilde{\Pi}_{\nu-\delta}$.

### Step 4: Bound $\|V\|$ and $\|VP_0\|$

**Depth factorization.** Every vector in $W_{\nu-\delta}$ decomposes as tensors with $\mu$-depth $\leq |\delta|$ and $\omega$-depth $\leq |\delta|$:

$$Q_{\nu-\delta} = Q_{\nu-\delta}(Q_{\leq|\delta|}^{(\mu)} \otimes Q_{\leq|\delta|}^{(\omega)})$$

On the shallow subspaces, the $\alpha$-string structure gives norm bounds for the root operators:
- $\|E_{\pm\alpha}^{(\mu)}\|_{\text{shallow}} = O(\sqrt{|\delta| \, n})$ (string length $\leq |\mu| = O(n)$)
- $\|E_{\pm\alpha}^{(\omega)}\|_{\text{shallow}} = O(\sqrt{|\delta| \, \|\omega\|})$ (string length $\leq \|\omega\|$)

Combining with the tensor structure and summing over finitely many positive roots:

$$\|V\| = O(|\delta| \sqrt{n \, \|\omega\|})$$

**Key trick for $\|VP_0\|$:** Since $|\omega\rangle$ is a highest-weight vector, $E_\alpha^{(\omega)}|\omega\rangle = 0$ for all positive roots $\alpha$. This kills half the perturbation terms on $P_0$, leaving only:

$$VP_0 = 2 Q_{\nu-\delta} \sum_{\alpha > 0} E_\alpha^{(\mu)} \otimes E_{-\alpha}^{(\omega)} P_0$$

Moreover, $|\omega\rangle$ sits at position $q = 0$ in every $\alpha$-string, so $\|E_{-\alpha}^{(\omega)}|\omega\rangle\|^2 = \langle\omega, \alpha^\vee\rangle \leq \|\omega\|$ -- a much tighter bound than the general shallow-depth estimate. This gives:

$$\|VP_0\| = O(\sqrt{n \, |\delta| \, \|\omega\|})$$

Note: $\|VP_0\| = O(\sqrt{n|\delta|\|\omega\|})$ is much smaller than $\|V\| = O(|\delta|\sqrt{n\|\omega\|})$ by a factor of $\sqrt{|\delta|}$. This is the payoff of using the tighter form of Davis-Kahan.

### Step 5: Apply Davis-Kahan

By the [[results/remaining-lemmas|Davis-Kahan Theorem (Lemma 6)]]:

$$\|\widetilde{\Pi}_{\nu-\delta} - \Pi_{\mu-\delta}^{(\omega)}\| = \|P - P_0\| \leq \frac{\|VP_0\|}{\Delta - \|V\|} = \frac{O(\sqrt{n \, |\delta| \, \|\omega\|})}{\Omega(n)} = O\left(\sqrt{\frac{|\delta| \, \|\omega\|}{n}}\right)$$

The condition $\|V\| \ll \Delta$ is satisfied since $\|V\| = O(|\delta|\sqrt{n\|\omega\|}) = o(n)$ under the assumption $|\delta|^2\|\omega\| \ll n$.

## Dependencies

- [[results/remaining-lemmas|Davis-Kahan Theorem (Lemma 6)]] -- the spectral perturbation theorem
- [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]] -- ensures $\mathrm{rank}(P_0) = \mathrm{rank}(P)$, i.e., $K_{\mu,\mu-\delta} = K_{\nu,\nu-\delta}$
- Casimir operator eigenvalue structure and $\alpha$-string norm bounds

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- Step 4 of the proof (quantum part of the fidelity)

## External References

- [Davis and Kahan, "The rotation of eigenvectors by a perturbation. III" (1970)](https://doi.org/10.1137/0707001)
- [Stewart and Sun, *Matrix Perturbation Theory* (Academic Press, 1990)](https://doi.org/10.1016/C2009-0-22288-3)
