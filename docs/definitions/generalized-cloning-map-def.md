# Generalized Cloning Map (Formal Definition)

**Source:** [[Article]], `eq:gen_cloner`, `prop:choi`; historical [[Notes]] definition.

## Statement

For $\mathrm{GL}(d, \mathbb{C})$ irreps with highest weights $\mu$ and $\nu$, let $\omega = (\nu - \mu)^+$ be the [[concepts/prv-component|PRV Component]] (the dominant rearrangement of $\nu - \mu$, appearing with multiplicity one in $\mu^* \otimes \nu$).

The **generalized cloning map** $C_{\mu \to \nu}: \mathcal{B}(H_\mu) \to \mathcal{B}(H_\nu)$ is defined by its Choi operator. When the difference $\nu-\mu$ is itself dominant, the equivalent Cartan formula is available:

**Cartan intertwiner form (dominant difference):**
$$C_{\mu \to \nu}(\sigma) = \frac{d_\mu}{d_\nu} V^\dagger (\sigma \otimes I_\omega) V$$

where $V: H_\nu \hookrightarrow H_\mu \otimes H_\omega$ is the intertwining isometry onto the Cartan component of highest weight $\nu=\mu+\omega$.

**Choi form:**
$$J = \frac{d_\mu}{d_\omega} \Pi_\omega$$

where $\Pi_\omega$ is the projector onto the PRV component in $H_{\mu^*} \otimes H_\nu$.

## Intuition

Tensor $\sigma$ with the maximally mixed state on $H_\omega$ (the "ancilla"), then project onto the PRV component in $H_\mu \otimes H_\omega$ that is isomorphic to $H_\nu$. Normalize so the output has unit trace.

## Concrete Qubit Example ($d = 2$)

**Setup:** Let $d = 2$, $\mu = (n, 0)$, $\nu = (m, 0)$ with $m > n$. These label the symmetric subspaces $\mathrm{Sym}^n(\mathbb{C}^2)$ and $\mathrm{Sym}^m(\mathbb{C}^2)$, which have dimensions $n + 1$ and $m + 1$ respectively.

**The PRV component:** After restriction to $\mathrm{SU}(2)$ (suppressing determinant twists), the decomposition of $\mu^* \otimes \nu$ reads:

$$\mu^* \otimes \nu \simeq \bigoplus_{k=0}^{\min(m,n)} \mathrm{Sym}^{|n-m|+2k}(\mathbb{C}^2)$$

The minimal (PRV) irrep is $\omega = (m - n, 0)$, corresponding to $\mathrm{Sym}^{m-n}(\mathbb{C}^2)$ with dimension $m - n + 1$.

**The map:** The isometry $V: \mathrm{Sym}^m(\mathbb{C}^2) \hookrightarrow \mathrm{Sym}^n(\mathbb{C}^2) \otimes \mathrm{Sym}^{m-n}(\mathbb{C}^2)$ embeds the "larger" symmetric subspace into the tensor product of the "smaller" one and the ancilla. The cloning map is:

$$\mathcal{C}_{(n,0) \to (m,0)}(\sigma) = \frac{n + 1}{m + 1} V^\dagger (\sigma \otimes I_{m-n}) V$$

This is exactly Werner's optimal cloning map from $n$ to $m$ copies of a qubit.

### Why the normalization $d_\mu / d_\nu$ makes the map trace-preserving

The Choi operator is $J_\omega = \frac{d_\mu}{d_\omega} \Pi_\omega$, where $\Pi_\omega$ projects onto the PRV component in $H_{\mu^*} \otimes H_\nu$. To check trace preservation, we need $\mathrm{Tr}_\nu(J_\omega) = I_{\mu^*}$.

The key argument uses Schur's lemma: since $\Pi_\omega$ commutes with the joint group action $U_{\mu^*}(g) \otimes U_\nu(g)$, its partial trace $\mathrm{Tr}_\nu(\Pi_\omega)$ must commute with $U_{\mu^*}(g)$ for all $g$. Since $\mu^*$ is irreducible, Schur's lemma forces $\mathrm{Tr}_\nu(\Pi_\omega) = c \cdot I_{\mu^*}$. Taking traces on both sides: $d_\omega = c \cdot d_\mu$, so $c = d_\omega / d_\mu$. Therefore:

$$\mathrm{Tr}_\nu(J_\omega) = \frac{d_\mu}{d_\omega} \cdot \frac{d_\omega}{d_\mu} I_{\mu^*} = I_{\mu^*}$$

The factor $d_\mu / d_\nu$ in the Cartan form (equivalently $d_\mu / d_\omega$ in the Choi form) is thus precisely the ratio needed to compensate for the "size mismatch" between the input and output irreps, ensuring the map sends unit-trace operators to unit-trace operators.

## Further Examples

- $\mu = \nu$: $\omega$ is the trivial irrep, and $\mathcal{C}_{\mu \to \mu}$ is the identity channel.
- $\omega = (c, c, \ldots, c)$ (scalar shift): cloning map is the identity (up to relabeling).

## Connection to Proof Architecture

The generalized cloning map is the key technical ingredient enabling the compression scheme to work for qudits. In the [[results/achievability|Achievability (State Compression)]], the encoder measures a Young diagram $\lambda$ and applies $\mathcal{C}_{\lambda \to \Lambda^*}$ to map the measured irrep state $\rho_\lambda$ to a universal target $\Lambda^*$. The decoder reverses this with $\mathcal{C}_{\Lambda^* \to \lambda'}$. [[results/cloning-fidelity|Article Theorem 2]] gives direct trace error $C_{d,x}\|\nu-\mu\|_1/(b_\mu+1)$ in both directions for the supported Cartan pairs. The current physical protocol uses replacement channels for atypical sectors.

## Formal Scope

`Theorem2Choi` identifies the literal Choi contraction with the constructed CPTP channels on all input matrices. Both projectors have proved multiplicity one and highest-weight labels; the reverse label is $-w_0(\nu-\mu)$. The construction permits signed dominant differences, and `CanonicalCloningSelf` proves that the Cartan formulas themselves are the identity at $\mu=\nu$. It does not claim a construction for every arbitrary nondominant pair. See [[proof-structure]].

## Used By

- [[concepts/generalized-cloning-map|Generalized Cloning Map]] (concept page)
- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]]
- [[results/achievability|Achievability (State Compression)]]

## External References

- [Werner, "Optimal cloning of pure states" (1998)](https://doi.org/10.1103/PhysRevA.58.1827)
- [Quantum cloning (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_cloning)
