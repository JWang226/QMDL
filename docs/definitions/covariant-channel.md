# $U(d)$-Covariant Channel

**Source:** Article line ~269; Notes line ~323

## Statement

A quantum channel $\mathcal{N}: \mathcal{B}(H_\mu) \to \mathcal{B}(H_\nu)$ between $\mathrm{GL}(d)$ irreps is **$U(d)$-covariant** if:

$$\mathcal{N}(\pi_\mu(U) \sigma \pi_\mu(U)^\dagger) = \pi_\nu(U) \mathcal{N}(\sigma) \pi_\nu(U)^\dagger \quad \forall U \in U(d)$$

where $\pi_\mu, \pi_\nu$ are the representations of $U(d)$ on $H_\mu, H_\nu$.

## Intuition

The channel "commutes with rotations": **rotating the input is the same as rotating the output**. Physically, this means the channel does not "see" any preferred basis -- it treats all orientations of the state equally. If Alice rotates her input state by some unitary $U$ before sending it through the channel, the result is the same as if she sent the original state and Bob rotated the output by $U$.

This is the natural symmetry requirement for any channel used in the compression scheme: since the state $\rho = U \rho_0 U^\dagger$ has an unknown eigenbasis (parameterized by $U \in U(d)$), the encoder and decoder must handle all eigenbases equally. A covariant channel automatically respects this symmetry.

## Classification

By Schur's lemma, any $U(d)$-covariant channel from $H_\mu$ to $H_\nu$ is characterized by its Choi operator, which must be a positive operator on $H_\nu \otimes H_{\mu^*}$ that is $U(d)$-invariant. The irreducible $U(d)$-invariant subspaces in $H_\nu \otimes H_{\mu^*}$ give the possible "building blocks." Decomposing:

$$\mu^* \otimes \nu \simeq \bigoplus_\lambda \lambda$$

the Choi operator must be a convex combination of projectors onto these irreps:

$$J_{\mathcal{N}} = \bigoplus_\lambda c_\lambda \frac{d_\mu}{d_\lambda} \Pi_\lambda, \quad \sum_\lambda c_\lambda = 1, \quad c_\lambda \geq 0$$

The [[concepts/generalized-cloning-map|Generalized Cloning Map]] uses the **minimal** such block (the [[concepts/prv-component|PRV Component]]) -- the irrep $\omega = (\nu - \mu)^+$ that is dominated by every other irrep in the decomposition.

## Qubit Example: Werner's Cloner as the Unique Covariant Channel

For $d = 2$, the irreps $\mu = (n, 0)$ and $\nu = (m, 0)$ correspond to $\mathrm{Sym}^n(\mathbb{C}^2)$ and $\mathrm{Sym}^m(\mathbb{C}^2)$ -- the spaces of $n$ and $m$ symmetric qubits.

The decomposition $\mu^* \otimes \nu$ contains irreps $\mathrm{Sym}^{|n-m|+2k}(\mathbb{C}^2)$ for $k = 0, \ldots, \min(m,n)$. The minimal irrep ($k = 0$) gives Werner's cloner $\mathcal{C}_{n \to m}$, which is the **unique** $U(2)$-covariant channel from $\mathrm{Sym}^n$ to $\mathrm{Sym}^m$ that uses only the PRV component. This is the optimal approximate cloning map for pure qubits.

The covariance property $\mathcal{C}_{n \to m}(U^{\otimes n} \sigma U^{\dagger \otimes n}) = U^{\otimes m} \mathcal{C}_{n \to m}(\sigma) U^{\dagger \otimes m}$ means: cloning and then rotating gives the same result as rotating and then cloning.

## Connection to Proof Architecture

Covariance is the design principle behind the [[definitions/generalized-cloning-map-def|Generalized Cloning Map]]. The [[results/propositions/commutativity|Commutativity (Prop 3)]] shows that any $U(d)$-covariant channel automatically satisfies $[\mathcal{N}(\rho_\mu), \rho_\nu] = 0$, meaning the cloned state commutes with the target state. This implies the cloning error is purely in the eigenvalues, not in the eigenbasis -- a key simplification for the [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] proof.

## Used By

- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[results/propositions/commutativity|Commutativity (Prop 3)]]

## External References

- [Covariant quantum channel (Wikipedia)](https://en.wikipedia.org/wiki/Covariant_quantum_channel)
- [Holevo, *Probabilistic and Statistical Aspects of Quantum Theory* (Springer, 2011)](https://doi.org/10.1007/978-88-7642-378-9)
