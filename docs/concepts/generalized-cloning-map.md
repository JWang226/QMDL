# Generalized Cloning Map

**Appears in:** [[Article]] (Sec. 3), [[Letter]]

## Intuition

Werner's optimal cloning map takes a state in the symmetric subspace $\mathrm{Sym}^n(\mathbb{C}^2)$ and "clones" it into $\mathrm{Sym}^m(\mathbb{C}^2)$ for $m > n$, achieving the best possible fidelity. The generalized cloning map extends this from symmetric subspaces (a single row of Young diagrams) to **arbitrary** $\mathrm{GL}(d, \mathbb{C})$ irreducible representations.

Think of it as: given a quantum state living in one irrep $H_\mu$, map it to a nearby irrep $H_\nu$ as faithfully as possible, using a $U(d)$-covariant quantum channel. The covariance requirement (commuting with all unitaries) essentially forces the channel to be determined by representation-theoretic data alone -- there is no room for ad hoc choices.

## Formal Definition

For GL$(d)$ irreps $\mu$ and $\nu$ with $\omega = (\nu - \mu)^+$ being the [[concepts/prv-component|PRV Component]] (the Cartan/dominant component in $\mu^* \otimes \nu$):

$$C_{\mu \to \nu}(\sigma) = \frac{d_\mu}{d_\nu} V^\dagger (\sigma \otimes I_\omega) V$$

where $V: H_\nu \hookrightarrow H_\mu \otimes H_\omega$ is the intertwining isometry onto the PRV component.

**Equivalently**, via the Choi operator:

$$J = \frac{d_\mu}{d_\omega} \Pi_\omega$$

where $\Pi_\omega$ is the projector onto the PRV component in $H_{\mu^*} \otimes H_\nu$.

### Why the PRV component?

Any $U(d)$-covariant channel $\mathcal{N}: \mathcal{B}(H_\mu) \to \mathcal{B}(H_\nu)$ has a Choi operator $J_\mathcal{N}$ that commutes with $U_{\mu^*}(g) \otimes U_\nu(g)$. By Schur's lemma, $J_\mathcal{N}$ must be a convex combination of projectors onto the irreducible summands of $\mu^* \otimes \nu$:

$$J_\mathcal{N} \simeq \bigoplus_\lambda c_\lambda \frac{d_\mu}{d_\lambda} \Pi_\lambda, \quad \sum_\lambda c_\lambda = 1, \quad c_\lambda \geq 0$$

To preserve the most information, we pick the **minimal** irrep under the dominance (majorization) ordering. This minimum is unique and is exactly the PRV component $\omega = (\nu - \mu)^+$. It appears with multiplicity one (by [[concepts/kumars-theorem|Kumar's Theorem]]), so the cloning map is uniquely determined up to phase. Using the smallest ancilla means the channel leaks the least information to the environment.

## Proof That the Channel Is Trace-Preserving

The map is completely positive because its Choi operator $J_\omega = (d_\mu/d_\omega)\Pi_\omega$ is proportional to a projector. To verify trace-preservation, we need $\mathrm{Tr}_\nu(J_\omega) = I_{\mu^*}$. The argument proceeds in three clean steps:

1. **Covariance of the partial trace.** Since $\Pi_\omega$ projects onto an invariant subspace of $\mu^* \otimes \nu$, it commutes with $U_{\mu^*}(g) \otimes U_\nu(g)$ for all $g \in U(d)$. Tracing over $\nu$ preserves this covariance, so $\mathrm{Tr}_\nu(\Pi_\omega)$ commutes with $U_{\mu^*}(g)$ for all $g$.

2. **Schur's lemma forces proportionality.** Since $\mu^*$ is irreducible, any operator commuting with all $U_{\mu^*}(g)$ must be a scalar multiple of the identity: $\mathrm{Tr}_\nu(\Pi_\omega) = c \cdot I_{\mu^*}$.

3. **Fix the constant by taking the trace.** Taking the trace of both sides: $\mathrm{Tr}(\Pi_\omega) = d_\omega$ on the left and $c \cdot d_\mu$ on the right, giving $c = d_\omega / d_\mu$. Substituting back: $\mathrm{Tr}_\nu(J_\omega) = (d_\mu/d_\omega) \cdot (d_\omega/d_\mu) \cdot I_{\mu^*} = I_{\mu^*}$.

## Concrete Example: GL(3)

Take $\mu = (5, 3, 1)$ and $\nu = (6, 4, 2)$. Then:
- $\omega = \nu - \mu = (1, 1, 1)$, which is already dominant.
- The irrep $(1, 1, 1)$ is the **determinant representation** of GL(3), which is 1-dimensional!
- So the cloning map $C_{\mu \to \nu}$ has a 1-dimensional ancilla -- the Choi operator is rank 1.
- In the Stinespring picture, $V: H_\nu \to H_\mu \otimes H_{(1,1,1)}$ is literally an isometry onto a 1-dimensional ancilla factor, making the channel as close to reversible as a covariant map can be.

This illustrates why cloning between "parallel" irreps (those differing by a multiple of $(1,\ldots,1)$) is especially efficient.

## Key Properties

### 1. Reduces to Werner's Cloner for Qubits
When $d = 2$, $\mu = (n, 0)$, $\nu = (m, 0)$ (symmetric subspaces), this recovers Werner's optimal cloning map $\mathrm{Sym}^n \to \mathrm{Sym}^m$. The decomposition $\mu^* \otimes \nu \simeq \bigoplus_{k=0}^{\min(m,n)} \mathrm{Sym}^{|n-m+2k|}(\mathbb{C}^2)$ has minimal element $\mathrm{Sym}^{|m-n|}(\mathbb{C}^2)$, matching the YCH construction.

### 2. Minimal Covariant Channel
Among all $U(d)$-covariant channels from $H_\mu$ to $H_\nu$, this uses the **smallest possible** ancilla system $H_\omega$ (in the dominance ordering). Note that "minimal" and "smallest dimension" are not the same -- the PRV component is minimal under majorization but may not have the smallest dimension among summands. For instance, with $\mu = (1,0,0)$ and $\nu = (5,1,0)$ in GL(3), the PRV component $\omega = (4,1,0)$ has dimension 24, while the summand $(5,0,0)$ has dimension 21.

### 3. Reverse Cloner = Petz Recovery Map
The Petz recovery map of $C_{\mu \to \nu}$ with respect to the maximally mixed state $I/d_\mu$ is exactly the reverse cloning map $C_{\nu \to \mu}$:

$$C_{\nu \to \mu}(X) = \frac{d_\nu}{d_\mu} C_{\mu \to \nu}^\dagger(X) = \mathrm{Tr}_\omega(V X V^\dagger)$$

See [[results/remaining-lemmas|Reverse Cloner (Prop 2)]].

### 4. Output Commutes with Target
For any $U(d)$-covariant channel, $[C_{\mu \to \nu}(\rho_\mu), \rho_\nu] = 0$. The output always commutes with the target state, so the cloner only distorts eigenvalues, not eigenbases. See [[results/remaining-lemmas|Commutativity (Prop 3)]].

### 5. High Fidelity When Irreps Are Close
The central technical result: when $|\mu|, |\nu| = \Theta(n)$ and $d(\mu, \nu) = \sum_i |\mu_i - \nu_i|$, for any arbitrarily small $\varepsilon > 0$:

$$F(C_{\mu \to \nu}(\rho_\mu), \rho_\nu) \geq 1 - O\left(\frac{d(\mu, \nu)}{n^{1-\varepsilon}}\right)$$

The proof decomposes the fidelity into a classical part (ratio of Schur polynomials, controlled by [[results/remaining-lemmas|Probability Ratio (Lemma 10)]]) and a quantum part (alignment of weight spaces, controlled by the [[concepts/casimir-operator|Casimir Operator]] perturbation analysis). See [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]].

## Role in the Project

The generalized cloning map is the **key technical innovation** that makes the compression scheme work. In the compression protocol:

1. Apply the [[concepts/schur-transform|Schur Transform]] to get sectors labeled by [[concepts/young-diagrams|Young Diagrams]] $\lambda$
2. Measure $\lambda$, then discard the multiplicity register $M_\lambda$ (it carries no eigenbasis information)
3. For each typical $\lambda$, use $C_{\lambda \to \Lambda^*}$ to map to a single target irrep $\Lambda^*$
4. Store the result in $H_{\Lambda^*}$ (the compressed memory)
5. To decompress, use the reverse cloner $C_{\Lambda^* \to \lambda}$

The cloning fidelity theorem guarantees this works with error $O(n^{-1/4+\varepsilon})$ on typical sectors, while the atypical tail is exponentially suppressed by Sanov's theorem.

## Related

- [[concepts/prv-component|PRV Component]] -- the ancilla irrep $\omega = (\nu - \mu)^+$
- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- the main fidelity bound
- [[results/remaining-lemmas|Reverse Cloner (Prop 2)]] -- Petz recovery interpretation
- [[results/remaining-lemmas|Commutativity (Prop 3)]] -- structural property
- [[concepts/werners-cloning-map|Werner's Cloning Map]] -- the qubit special case
- [[concepts/casimir-operator|Casimir Operator]] -- key tool in the fidelity proof
- [[concepts/kumars-theorem|Kumar's Theorem]] -- multiplicity-one guarantee
- [[results/achievability|Achievability (State Compression)]] -- how the cloner is used

## External References

- [Werner, "Optimal cloning of pure states, testing single clones" (1998)](https://arxiv.org/abs/quant-ph/9804001)
- [Keyl and Werner, "Optimal cloning of pure states, judging single clones" (1999)](https://arxiv.org/abs/quant-ph/9910053)
- [Quantum cloning (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_cloning)
