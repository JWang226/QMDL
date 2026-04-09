# Petz Recovery Map

**Appears in:** Article (Prop. 2)

## Definition

For a quantum channel $\mathcal{N}: A \to B$ and a state $\sigma$ on $A$, the **Petz recovery map** is:

$$\mathcal{R}_{\sigma, \mathcal{N}}(X) = \sigma^{1/2} \mathcal{N}^\dagger\left(\mathcal{N}(\sigma)^{-1/2} X \mathcal{N}(\sigma)^{-1/2}\right) \sigma^{1/2}$$

where $\mathcal{N}^\dagger$ is the adjoint channel.

## Why the Petz Map is "Best Possible"

The Petz recovery map has a fundamental optimality property rooted in the **data processing inequality** (DPI). Recall that the DPI says: for any channel $\mathcal{N}$ and any two states $\rho, \sigma$:

$$D(\rho \| \sigma) \geq D(\mathcal{N}(\rho) \| \mathcal{N}(\sigma))$$

where $D$ is the quantum relative entropy. Equality holds if and only if the channel $\mathcal{N}$ is **reversible on the pair $(\rho, \sigma)$** -- meaning there exists a recovery channel $\mathcal{R}$ such that $\mathcal{R} \circ \mathcal{N}(\rho) = \rho$ and $\mathcal{R} \circ \mathcal{N}(\sigma) = \sigma$. When equality holds, the Petz map $\mathcal{R}_{\sigma, \mathcal{N}}$ is exactly such a recovery channel.

More generally, even when the DPI is not saturated (strict inequality), the Petz map is the "least distorting" recovery: it achieves the best possible fidelity for recovering $\sigma$ after the action of $\mathcal{N}$, among all recovery maps that depend on $\sigma$ and $\mathcal{N}$ but not on the unknown input state.

## Role in the Project

**Proposition 2 (Reverse Cloner)** in the Article shows that the Petz recovery map of the [[concepts/generalized-cloning-map|Generalized Cloning Map]] $C_{\mu \to \nu}$ with respect to the maximally mixed state $\sigma = I/d_\mu$ is exactly the reverse cloning map:

$$\mathcal{R}_{I/d_\mu, C_{\mu\to\nu}} = C_{\nu \to \mu}$$

This is a beautiful structural result: the forward and reverse cloners are Petz duals of each other. It gives a **quantum error correction interpretation** of the compression scheme -- the decoder (reverse cloner) is the optimal recovery operation for the encoder (forward cloner). This also explains why the scheme works: the Petz map recovers the original state perfectly when the channel is reversible on the given state, and near-perfectly when the channel is approximately reversible (which happens when $\mu$ and $\nu$ are close).

## Related

- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[results/reverse-cloner|Reverse Cloner (Prop 2)]]

## External References

- [Petz recovery map (Wikipedia)](https://en.wikipedia.org/wiki/Petz_recovery_map)
- D. Petz, "Sufficient subalgebras and the relative entropy of states of a von Neumann algebra," *Comm. Math. Phys.* 105, 123--131 (1986)
- D. Petz, "Sufficiency of channels over von Neumann algebras," *Quart. J. Math. Oxford* 39, 97--108 (1988)
