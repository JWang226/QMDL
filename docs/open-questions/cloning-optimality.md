# Open: Optimality of the Generalized Cloning Map

**Source:** Article line ~435
**Status:** Open (conjecture)

## Context

The [[concepts/generalized-cloning-map|Generalized Cloning Map]] $\mathcal{C}_{\mu \to \nu}$ is defined via the PRV component -- the minimal irrep $\omega = (\nu - \mu)^+$ appearing in $\mu^* \otimes \nu$. Among all $U(d)$-covariant channels from $\mathcal{B}(\mathcal{H}_\mu)$ to $\mathcal{B}(\mathcal{H}_\nu)$, this map uses the smallest ancilla (in the dominance ordering), and it is uniquely determined by [[concepts/kumars-theorem|Kumar's Theorem]] (multiplicity one).

The paper proves that this channel achieves high fidelity $F(\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu) \geq 1 - O(d(\mu,\nu)/n^{1-\varepsilon})$ ([[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]]). However, it does **not** prove that this is the best possible among all covariant channels.

## Conjecture

Among all $U(d)$-covariant channels $\mathcal{N}: \mathcal{B}(\mathcal{H}_\mu) \to \mathcal{B}(\mathcal{H}_\nu)$, the generalized cloning map maximizes the cloning fidelity:

$$F(\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu) \geq F(\mathcal{N}(\rho_\mu), \rho_\nu) \quad \text{for all covariant } \mathcal{N}$$

More precisely, the conjecture (stated in the Article after Prop 3) is that the PRV channel maximizes the overlap $\mathrm{Tr}(\mathcal{N}(\rho_\mu) \rho_\nu)$.

## Why It Should Be True

The intuition is that using the **smallest ancilla** means the channel leaks the least information to the environment. Any covariant channel has Choi operator $J_\mathcal{N} = \bigoplus_\lambda c_\lambda (d_\mu/d_\lambda) \Pi_\lambda$ supported on irreps $\lambda$ in $\mu^* \otimes \nu$. The PRV channel concentrates all weight on the minimal $\lambda = \omega$. Mixing in larger irreps should only hurt fidelity, since larger ancillas carry more information away from the output.

For qubits ($d = 2$), this is known: Werner's cloning map (which is the PRV channel for symmetric subspaces) is optimal among covariant cloners.

## Why It Is Hard

The general proof would need to show that for any convex combination $J_\mathcal{N} = \sum_\lambda c_\lambda (d_\mu/d_\lambda) \Pi_\lambda$, the fidelity is maximized when $c_\omega = 1$ and all other $c_\lambda = 0$. This requires understanding how the different irreducible components in $\mu^* \otimes \nu$ interfere when computing fidelity -- a problem that involves detailed Clebsch-Gordan coefficient structure beyond what is currently used in the proofs.

## Impact

If true, this would strengthen the compression result: the achievability protocol using the PRV cloner would be provably optimal not just at the rate level but also among all covariant encoding strategies. It would also provide a representation-theoretic characterization of optimal approximate cloning for general groups.

## Related

- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- the channel whose optimality is conjectured
- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- the current fidelity bound
- [[concepts/prv-component|PRV Component]] -- the minimal irrep $\omega = (\nu - \mu)^+$
- [[concepts/kumars-theorem|Kumar's Theorem]] -- uniqueness (multiplicity one) of the PRV component
- [[concepts/werners-cloning-map|Werner's Cloning Map]] -- the qubit case where optimality is known

## External References

- [Werner, "Optimal cloning of pure states" (1998)](https://doi.org/10.1103/PhysRevA.58.1827)
- [Scarani et al., "Quantum cloning" (2005)](https://doi.org/10.1103/RevModPhys.77.1225)
- [Quantum cloning (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_cloning)
