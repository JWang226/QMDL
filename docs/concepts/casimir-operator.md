# Casimir Operator

**Appears in:** [[Article]] (Sec. 6)

## Definition

The **quadratic Casimir operator** for $\mathfrak{gl}(d)$ in the Cartan-Weyl basis is:

$$C_2 = \sum_{i=1}^d H_i^2 + \sum_{\alpha \in \Phi^+} (E_{-\alpha} E_\alpha + E_\alpha E_{-\alpha})$$

where $H_i$ are the Cartan generators (diagonal matrices) and $E_{\pm\alpha}$ are the raising/lowering operators for positive roots $\alpha$.

On the irrep $H_\lambda$, the Casimir acts as a scalar: $C_2(\lambda) = (\lambda, \lambda + 2\varrho)$, where $\varrho = \frac{1}{2}\sum_{\alpha \in \Phi^+} \alpha$ is the Weyl vector.

## Intuition

The Casimir is the representation-theoretic analogue of the total angular momentum operator $\mathbf{J}^2$ in quantum mechanics. Just as $\mathbf{J}^2$ has a fixed eigenvalue on each spin-$j$ representation, $C_2$ has a fixed eigenvalue on each irrep $H_\lambda$. This makes it a perfect tool for **distinguishing irreps**: different irreps have different Casimir eigenvalues, with gaps that grow with the size of the representation.

In the cloning fidelity proof, the Casimir plays the role of a Hamiltonian whose spectral structure lets us control how the weight spaces of a tensor product align with those of a single irrep.

## The Perturbation Analysis (Article Sec. 6)

This is the core technical argument that controls the "quantum contribution" to the [[results/cloning-fidelity|cloning fidelity]]. The goal is to show that the weight spaces of $H_\nu$ (embedded in $H_\mu \otimes H_\omega$) are close to the "naive" product weight spaces $W_{\mu-\delta} \otimes |\omega\rangle$.

### Setup

We work on the product space $H_\mu \otimes H_\omega$ where $\nu = \mu + \omega$. The total quadratic Casimir decomposes as:

$$C_2^{(\nu)} = C_2^{(\mu)} \otimes I + I \otimes C_2^{(\omega)} + 2\sum_{i=1}^d H_i^{(\mu)} \otimes H_i^{(\omega)} + 2\sum_{\alpha > 0}\left(E_{-\alpha}^{(\mu)} \otimes E_\alpha^{(\omega)} + E_\alpha^{(\mu)} \otimes E_{-\alpha}^{(\omega)}\right)$$

The first three terms are **diagonal** in the product weight basis (they depend only on which weights you are in). The last term contains **off-diagonal root-exchange** operators that couple different product weight spaces.

### Splitting into $H_0 + V$

Restrict everything to a fixed total-weight slice $W_{\nu - \delta}$ (all states with total weight $\nu - \delta$). Define:

**Unperturbed part $H_0$:** The diagonal terms (Casimir scalars + Cartan cross terms):

$$H_0 = C_2(\mu) + C_2(\omega) + 2\sum_i H_i^{(\mu)} \otimes H_i^{(\omega)}\Big|_{W_{\nu-\delta}}$$

On the subspace $\Pi_{\mu-\delta} \otimes |\omega\rangle\langle\omega|$ (where $\omega$-register is at its highest weight), $H_0$ acts with eigenvalue:

$$\lambda_0 = C_2(\mu) + C_2(\omega) + 2(\mu - \delta, \omega)$$

**Perturbation $V$:** The off-diagonal root-exchange terms:

$$V = 2\sum_{\alpha > 0}\left(E_{-\alpha}^{(\mu)} \otimes E_\alpha^{(\omega)} + E_\alpha^{(\mu)} \otimes E_{-\alpha}^{(\omega)}\right)\Big|_{W_{\nu-\delta}}$$

### The spectral gap is $\Theta(n)$

Any state orthogonal to $\mathrm{im}(P_0) = \Pi_{\mu-\delta} \otimes |\omega\rangle$ in the weight slice $W_{\nu-\delta}$ must have the $\omega$-register at a **lower** weight $\omega - \eta$ (with $\eta \neq 0$), forcing the $\mu$-register to weight $\mu - \delta + \eta$ to maintain the total weight. On such a product weight space, $H_0$ has eigenvalue:

$$\lambda_1(\eta) = C_2(\mu) + C_2(\omega) + 2(\mu - \delta + \eta, \omega - \eta)$$

The gap between the distinguished eigenvalue and any competitor is:

$$\lambda_0 - \lambda_1(\eta) = 2(\mu, \eta) - 2(\delta, \eta) - 2(\omega, \eta) + 2(\eta, \eta)$$

Now bound each term using the root structure of type $A_{d-1}$:
- $(\mu, \eta) \geq g_\mu |\eta|$ where $g_\mu = \min_i(\mu_i - \mu_{i+1})$ is the **edge gap** -- this is the dominant term, of order $\Theta(n)$
- $|(\delta, \eta)| \leq 2|\delta||\eta|$ -- subleading since $|\delta| = o(n)$
- $|(\omega, \eta)| \leq \|\omega\||\eta|$ where $\|\omega\| = \omega_1 - \omega_d$ -- subleading since $\|\omega\| = o(n)$
- $(\eta, \eta) \geq 0$ -- helps the gap

This gives:

$$\Delta = \min_{\eta \neq 0}(\lambda_0 - \lambda_1(\eta)) \geq |\eta|(2g_\mu - 4|\delta| - 2\|\omega\|) = \Theta(n)$$

### The key trick: bounding $\|VP_0\|$

The full perturbation norm $\|V\|$ is too large -- it scales as $O(|\delta|\sqrt{n\|\omega\|})$. But the Davis-Kahan $\sin\theta$ theorem only needs $\|VP_0\|$, the perturbation **restricted to the unperturbed eigenspace**. This is where the highest-weight structure saves us.

On $P_0 = \Pi_{\mu-\delta} \otimes |\omega\rangle\langle\omega|$, the $\omega$-register sits at the highest weight $|\omega\rangle$. Since $|\omega\rangle$ is a highest-weight vector:

$$E_\alpha^{(\omega)}|\omega\rangle = 0 \quad \text{for all } \alpha > 0$$

So the raising operators on $\omega$ annihilate $P_0$, and **only the lowering terms survive**:

$$VP_0 = 2\sum_{\alpha > 0} E_\alpha^{(\mu)} \otimes E_{-\alpha}^{(\omega)} \cdot P_0$$

The lowering operator $E_{-\alpha}^{(\omega)}$ on the highest-weight vector satisfies $\|E_{-\alpha}^{(\omega)}|\omega\rangle\|^2 = \langle\omega, \alpha^\vee\rangle \leq \|\omega\|$, giving:

$$\|VP_0\| = O(\sqrt{n \cdot |\delta| \cdot \|\omega\|})$$

### Applying Davis-Kahan

The Davis-Kahan $\sin\theta$ theorem (Lemma 6) gives:

$$\|\widetilde{\Pi}_{\nu-\delta} - \Pi_{\mu-\delta}^{(\omega)}\| \leq \frac{\|VP_0\|}{\Delta - \|V\|} = \frac{O(\sqrt{n \cdot |\delta| \cdot \|\omega\|})}{\Omega(n)} = O\left(\sqrt{\frac{|\delta| \cdot \|\omega\|}{n}}\right)$$

This says: the weight spaces of the embedded $H_\nu$ (the "true" coupled subspaces) are close to the naive tensor products $W_{\mu-\delta} \otimes |\omega\rangle$ (the "uncoupled" subspaces), with an error that goes to zero as $n \to \infty$.

### What this means for the cloning fidelity

The principal angles $\theta_i$ between the true and naive weight spaces satisfy $\sin\theta_{\max} = O(\sqrt{|\delta|\|\omega\|/n})$. The block fidelity then satisfies:

$$F_{\mathrm{block}}(\delta) \geq \sqrt{d_\mu/d_\nu} \cdot m(\delta) \cdot (1 - O(|\delta|\|\omega\|/n))$$

Summing over weight offsets $\delta$ up to a cutoff $T = O(n^\varepsilon)$ and using the tail bound (Lemma 8) for higher weights, one obtains the full cloning fidelity $\geq 1 - O(d(\mu,\nu)/n^{1-\varepsilon})$.

## Summary of Scaling

| Quantity | Scale | Role |
|---|---|---|
| Spectral gap $\Delta$ | $\Theta(n)$ | Separation of the target eigenspace |
| Perturbation $\|V\|$ | $O(|\delta|\sqrt{n\|\omega\|})$ | Full off-diagonal strength |
| Restricted perturbation $\|VP_0\|$ | $O(\sqrt{n \cdot |\delta| \cdot \|\omega\|})$ | Exploits highest-weight annihilation |
| Weight space mismatch | $O(\sqrt{|\delta|\|\omega\|/n})$ | Goes to 0 as $n \to \infty$ |

## Related

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- the theorem this analysis supports
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- the channel whose fidelity is being bounded
- [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin Basis]] -- provides the weight space structure
- [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]] -- the formal statement

## External References

- [Casimir element (Wikipedia)](https://en.wikipedia.org/wiki/Casimir_element)
- J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Graduate Texts in Mathematics, Springer (1972)
- B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, Graduate Texts in Mathematics, Springer (2015)
