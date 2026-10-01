# Petz Recovery Map

**Appears in:** [[Article]], `prop:reverse` (Reverse cloner).

## Definition

For a quantum channel $\mathcal{N}: A \to B$ and a state $\sigma$ on $A$, the **Petz recovery map** is:

$$\mathcal{R}_{\sigma, \mathcal{N}}(X) = \sigma^{1/2} \mathcal{N}^\dagger\left(\mathcal{N}(\sigma)^{-1/2} X \mathcal{N}(\sigma)^{-1/2}\right) \sigma^{1/2}$$

Here $\mathcal N^\dagger$ is the Hilbert–Schmidt adjoint map; inverse square roots are taken on the relevant support. For the maximally mixed canonical states used below, the inverses are ordinary inverses.

## Exact Recovery and Its Limits

The Petz recovery map has a fundamental optimality property rooted in the **data processing inequality** (DPI). Recall that the DPI says: for any channel $\mathcal{N}$ and any two states $\rho, \sigma$:

$$D(\rho \| \sigma) \geq D(\mathcal{N}(\rho) \| \mathcal{N}(\sigma))$$

where $D$ is the quantum relative entropy. Equality holds if and only if the channel $\mathcal{N}$ is **reversible on the pair $(\rho, \sigma)$** -- meaning there exists a recovery channel $\mathcal{R}$ such that $\mathcal{R} \circ \mathcal{N}(\rho) = \rho$ and $\mathcal{R} \circ \mathcal{N}(\sigma) = \sigma$. When equality holds, the Petz map $\mathcal{R}_{\sigma, \mathcal{N}}$ is exactly such a recovery channel.

This exact-recovery characterization does not say that the ordinary Petz map maximizes fidelity for every approximately reversible family. The project proves an approximation estimate for its specific representation-state family.

## Role in the Project

The **Reverse cloner proposition** in the Article shows that the Petz recovery map of the [[concepts/generalized-cloning-map|Generalized Cloning Map]] $C_{\mu \to \nu}$ with respect to the maximally mixed state $\sigma = I/d_\mu$ is exactly the reverse cloning map:

$$\mathcal{R}_{I/d_\mu, C_{\mu\to\nu}} = C_{\nu \to \mu}$$

`canonicalPetz_eq_reverse` in `CanonicalPetz.lean` proves the literal Petz formula agrees with the actual reverse cloner, using the normalized Hilbert–Schmidt adjoint and the image of the maximally mixed state. Article Theorem 2 separately proves the forward and reverse trace-distance estimates. The identity includes coincident rows and the signed auxiliary differences used by the construction; it does not claim optimal recovery among all channels. See [[proof-structure]].

## Related

- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[results/propositions/reverse-cloner|Reverse Cloner]]

## External References

- [Petz recovery map (Wikipedia)](https://en.wikipedia.org/wiki/Petz_recovery_map)
- D. Petz, "Sufficient subalgebras and the relative entropy of states of a von Neumann algebra," *Comm. Math. Phys.* 105, 123--131 (1986)
- D. Petz, "Sufficiency of channels over von Neumann algebras," *Quart. J. Math. Oxford* 39, 97--108 (1988)
