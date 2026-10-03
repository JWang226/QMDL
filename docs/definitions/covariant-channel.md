# $U(d)$-Covariant Channel

**Source:** current [[Article]], `eq:covariance` and `eq:covChoi`, in [the PRV-channel section](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L340); historical [[Notes]] background.

## Statement

A quantum channel $\mathcal{N}: \mathcal{B}(H_\mu) \to \mathcal{B}(H_\nu)$ between $\mathrm{GL}(d)$ irreps is **$U(d)$-covariant** if:

$$\mathcal{N}(\pi_\mu(U) \sigma \pi_\mu(U)^\dagger) = \pi_\nu(U) \mathcal{N}(\sigma) \pi_\nu(U)^\dagger \quad \forall U \in U(d)$$

where $\pi_\mu, \pi_\nu$ are the representations of $U(d)$ on $H_\mu, H_\nu$.

## Intuition

The channel "commutes with rotations": **rotating the input is the same as rotating the output**. Physically, this means the channel does not "see" any preferred basis -- it treats all orientations of the state equally. If Alice rotates her input state by some unitary $U$ before sending it through the channel, the result is the same as if she sent the original state and Bob rotated the output by $U$.

The constructed cloning channels satisfy this symmetry, making their error bounds uniform over the unknown eigenbasis. A general admissible compression code need only be fixed independently of the unknown unitary; covariance is not an extra assumption in the Article's converse.

## Classification

The Choi operator commutes with $U_{\mu^*}\otimes U_\nu$. If

$$H_{\mu^*}\otimes H_\nu\simeq\bigoplus_\lambda H_\lambda\otimes\mathbb C^{m_\lambda},$$

then Schur's lemma gives

$$J_{\mathcal N}\simeq\bigoplus_\lambda I_{H_\lambda}\otimes A_\lambda,\qquad A_\lambda\ge0,$$

with trace-preservation constraints. Multiplicity spaces cannot in general be replaced by scalar coefficients. A normalized projector onto a multiplicity-one component does give a channel; the [[concepts/generalized-cloning-map|generalized cloner]] uses the PRV component.

## Qubit Example: Selecting the PRV Channel

For $d = 2$, the irreps $\mu = (n, 0)$ and $\nu = (m, 0)$ correspond to $\mathrm{Sym}^n(\mathbb{C}^2)$ and $\mathrm{Sym}^m(\mathbb{C}^2)$ -- the spaces of $n$ and $m$ symmetric qubits.

After restriction to $\mathrm{SU}(2)$, the decomposition $\mu^* \otimes \nu$ contains irreps $\mathrm{Sym}^{|n-m|+2k}(\mathbb{C}^2)$ for $k = 0, \ldots, \min(m,n)$. The minimal irrep ($k = 0$) gives Werner's cloner $\mathcal{C}_{n \to m}$, which is the **unique** $U(2)$-covariant channel from $\mathrm{Sym}^n$ to $\mathrm{Sym}^m$ that uses only the PRV component. This is the optimal approximate cloning map for pure qubits.

The covariance property $\mathcal{C}_{n \to m}(U^{\otimes n} \sigma U^{\dagger \otimes n}) = U^{\otimes m} \mathcal{C}_{n \to m}(\sigma) U^{\dagger \otimes m}$ means: cloning and then rotating gives the same result as rotating and then cloning.

## Connection to Proof Architecture

Covariance is the design principle behind the [[definitions/generalized-cloning-map-def|Generalized Cloning Map]]. The [[results/propositions/commutativity|Commutativity]] shows that any $U(d)$-covariant channel automatically satisfies $[\mathcal{N}(\rho_\mu), \rho_\nu] = 0$, meaning the cloned state commutes with the target state. The two states can therefore be simultaneously diagonalized, although the output need not be scalar on each degenerate target weight space. The final formal proof derives covariance and its uniform orbit error directly; it does not claim a separate formal endpoint for the Article's general commutativity proposition.

## Used By

- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[results/propositions/commutativity|Commutativity]]

## External References

- [Covariant quantum channel (Wikipedia)](https://en.wikipedia.org/wiki/Covariant_quantum_channel)
- [Holevo, *Probabilistic and Statistical Aspects of Quantum Theory* (Springer, 2011)](https://doi.org/10.1007/978-88-7642-378-9)
