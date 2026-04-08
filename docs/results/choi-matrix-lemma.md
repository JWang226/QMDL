# Choi Matrix of the Minimal Covariant Channel

**Label:** `lem:choi_prv` (Notes)
**Source:** Notes line ~391; Article Prop. 1 (line ~372)

## Statement

Let $V: \mathcal{H}_\nu \to \mathcal{H}_\mu \otimes \mathcal{H}_\omega$ be the isometric embedding of the representation $\nu = \mu + \omega$ into $\mu \otimes \omega$, where $\omega = (\nu - \mu)^+$ is the [[concepts/prv-component|PRV Component]]. The $U(d)$-covariant channel

$$\mathcal{C}_{\mu \to \nu}(\rho) = \frac{d_\mu}{d_\nu} V^\dagger(\rho \otimes I_\omega) V$$

has Choi matrix

$$\mathsf{C} = \frac{d_\mu}{d_\omega} \Pi_\omega$$

where $\Pi_\omega$ is the projector onto the PRV component $\omega$ in $\mathcal{H}_\nu \otimes \mathcal{H}_{\mu^*}$.

## Intuition

The Choi matrix of a covariant channel must itself be covariant (i.e., invariant under the joint $U(d)$ action on $\nu \otimes \mu^*$). By [[concepts/kumars-theorem|Kumar's Theorem]], the PRV component $\omega = (\nu - \mu)^+$ appears with multiplicity one in $\nu \otimes \mu^*$, so Schur's lemma forces the Choi matrix to be proportional to $\Pi_\omega$. The proportionality constant is then fixed by the trace-preserving condition.

## Proof Sketch

**Main idea:** Reshuffle the Stinespring isometry $V$ into an intertwiner $\tilde{V}: \mathcal{H}_\nu \otimes \mathcal{H}_{\mu^*} \to \mathcal{H}_\omega$, so the Choi matrix becomes $\propto \tilde{V}^\dagger \tilde{V}$. Since $\tilde{V}$ is $U(d)$-equivariant and $\omega$ has multiplicity one in $\nu \otimes \mu^*$ (Kumar's theorem), Schur's lemma forces $\tilde{V}^\dagger \tilde{V} \propto \Pi_\omega$. The trace-preserving condition fixes the constant.

---

### Extended Proof

The proof proceeds through a Choi--Jamiolkowski computation with an explicit intertwiner.

**Step 1: Define the maximally entangled vector.** Introduce the unnormalized maximally entangled state on $\mathcal{H}_\mu \otimes \mathcal{H}_{\mu^*}$:

$$|\Omega\rangle = \sum_{M} |\mu, M\rangle \otimes |\mu^*, M^*\rangle$$

where the sum runs over a weight basis $\{|\mu, M\rangle\}$ of $\mathcal{H}_\mu$ and $\{|\mu^*, M^*\rangle\}$ is the corresponding dual basis.

**Step 2: Form the Choi operator.** By definition, the Choi matrix $\mathsf{C} \in \mathcal{B}(\mathcal{H}_\nu \otimes \mathcal{H}_{\mu^*})$ is obtained by applying the channel to one half of $|\Omega\rangle\langle\Omega|$:

$$\mathsf{C} = (\mathcal{C}_{\mu \to \nu} \otimes \mathrm{id})(|\Omega\rangle\langle\Omega|)$$

Substituting the Stinespring form $\mathcal{C}(\rho) = \frac{d_\mu}{d_\nu} V^\dagger(\rho \otimes I_\omega)V$ and expanding gives:

$$\mathsf{C} = \frac{d_\mu}{d_\nu} \sum_{M, M'} \sum_W \bigl( V^\dagger |\mu, M; \omega, W\rangle\langle\mu, M'; \omega, W| V \bigr) \otimes |\mu^*, M^*\rangle\langle\mu^*, M'^*|$$

**Step 3: Introduce the intertwiner.** Define a linear map $\tilde{V}: \mathcal{H}_\nu \otimes \mathcal{H}_{\mu^*} \to \mathcal{H}_\omega$ by

$$\tilde{V} |\nu, N; \mu^*, K^*\rangle = \langle\mu, K| V |\nu, N\rangle$$

This "reshuffles" the Stinespring isometry into a map whose domain is the Choi space $\nu \otimes \mu^*$. A direct computation of the matrix elements of $\tilde{V}^\dagger \tilde{V}$ shows:

$$\langle\nu, N; \mu^*, K^*| \tilde{V}^\dagger \tilde{V} |\nu, N'; \mu^*, L^*\rangle = \sum_W \langle\nu, N| V^\dagger |\mu, K; \omega, W\rangle \langle\mu, L; \omega, W| V |\nu, N'\rangle$$

Comparing term-by-term with the expression for $\mathsf{C}$, one obtains the operator identity:

$$\mathsf{C} = \frac{d_\mu}{d_\nu} \tilde{V}^\dagger \tilde{V}$$

**Step 4: Apply Schur's lemma.** Since $V$ is $U(d)$-equivariant (it intertwines the action of $U(d)$ on $\nu$ and on $\mu \otimes \omega$), the map $\tilde{V}$ is also $U(d)$-equivariant. Therefore $\tilde{V}^\dagger \tilde{V}$ commutes with the joint $U(d)$ action on $\nu \otimes \mu^*$. By [[concepts/kumars-theorem|Kumar's Theorem]], the irrep $\omega = (\nu - \mu)^+$ appears with multiplicity one in $\nu \otimes \mu^*$, so Schur's lemma forces:

$$\tilde{V}^\dagger \tilde{V} \propto \Pi_\omega$$

**Step 5: Fix the constant by trace.** Since $V$ is an isometry ($V^\dagger V = I_\nu$), one computes:

$$\mathrm{Tr}(\tilde{V}^\dagger \tilde{V}) = \sum_N \langle\nu, N| V^\dagger V |\nu, N\rangle = d_\nu$$

Since $\mathrm{Tr}(\Pi_\omega) = d_\omega$, the proportionality constant is $d_\nu / d_\omega$, giving $\tilde{V}^\dagger \tilde{V} = \frac{d_\nu}{d_\omega} \Pi_\omega$. Substituting back:

$$\mathsf{C} = \frac{d_\mu}{d_\nu} \cdot \frac{d_\nu}{d_\omega} \Pi_\omega = \frac{d_\mu}{d_\omega} \Pi_\omega$$

## Dependencies

- [[concepts/prv-component|PRV Component]] -- the unique minimal component $\omega = (\nu - \mu)^+$ in the tensor product $\nu \otimes \mu^*$
- [[concepts/kumars-theorem|Kumar's Theorem]] -- multiplicity-one guarantee, which is what allows Schur's lemma to pin down $\mathsf{C}$ up to a scalar
- Schur's lemma -- any operator commuting with an irreducible group action is proportional to a projector
- [[Stinespring Dilation]] -- the isometric form $V$ of the covariant channel

## Used By

- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- the Choi matrix identifies the cloning channel with a PRV projector
- [[results/remaining-lemmas|Reverse Cloner (Prop 2)]]
- [[results/cloning-fidelity|Cloning Fidelity]] -- the fidelity bounds rely on the explicit Choi form
