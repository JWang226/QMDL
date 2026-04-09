# Davis-Kahan Theorem (Lemma 6)

**Label:** `lem:davis_kahan`
**Source:** Article line ~1209; Notes line ~654

## Statement

Let $H_0$ and $H = H_0 + V$ be Hermitian on a finite-dimensional Hilbert space. Let $S_0, S_1$ partition $\mathrm{spec}(H_0)$ with spectral gap $\Delta = \min_{\lambda \in S_0, \lambda' \in S_1} |\lambda - \lambda'|$. Let $P_0$ project onto the eigenspace of $H_0$ for $S_0$. If $\|V\| < \Delta$, then the eigenvalues of $H$ split into corresponding sets $\sigma_0(H), \sigma_1(H)$ with gap $\geq \Delta - \|V\|$, and the spectral projector $P$ of $H$ onto $\sigma_0(H)$ satisfies:

$$\sin(\theta_{\max}) \equiv \|P - P_0\| \leq \frac{\|V P_0\|}{\Delta - \|V\|}$$

where $\theta_{\max}$ is the largest principal angle between $\mathrm{Im}(P)$ and $\mathrm{Im}(P_0)$.

## Intuition

When you perturb a Hermitian operator by a small $V$, its eigenspaces rotate. The Davis-Kahan theorem quantifies this rotation: the projector moves by at most $\|VP_0\|/(\Delta - \|V\|)$, where $\Delta$ is the spectral gap protecting the eigenspace. The key feature is the use of $\|VP_0\|$ (the "restricted perturbation") rather than $\|V\|$, which can be much tighter.

## Proof Sketch

The projector $P$ is defined constructively via the resolvent: $P = -\frac{1}{2\pi i} \oint_\Gamma (z - H)^{-1} dz$ where $\Gamma$ encloses $S_0$ but excludes $S_1$. The condition $\|V\| < \Delta$ ensures no eigenvalue of $H$ crosses $\Gamma$, so $P$ has the same rank as $P_0$ and depends continuously on $V$. The bound uses $\|VP_0\|$ rather than $\|V\|$.

## Dependencies

- Standard spectral theory (resolvent integral)

## Used By

- [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]] -- applied with spectral gap $\Delta = \Theta(n)$ from the [[concepts/casimir-operator|Casimir]] eigenvalue structure and restricted perturbation $\|VP_0\| = O(\sqrt{n|\delta|\|\omega\|})$

## External References

- [Davis and Kahan, "The rotation of eigenvectors by a perturbation. III" (1970)](https://doi.org/10.1137/0707001)
