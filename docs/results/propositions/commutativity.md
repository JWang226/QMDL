# Commutativity (Proposition 3)

**Label:** `prop:commutativity` (Article), `lem:commutativity` (Notes)
**Source:** Article line ~421 (stated), ~2190 (proved); Notes line ~862

## Statement

For any $\mathrm{U}(d)$-covariant channel $\mathcal{C}_{\mu \to \nu}$:

$$[\mathcal{C}_{\mu \to \nu}(\rho_\mu), \rho_\nu] = 0$$

## Intuition

The output of any covariant cloning map commutes with the target state. This means both operators are simultaneously diagonalizable in the weight basis, reducing the fidelity computation to a classical (diagonal) sum over weight blocks.

## Proof Sketch

Work in the eigenbasis of $\rho$ where $\rho = \Lambda$ is diagonal. Both $\rho_\mu \propto \pi_\mu(\Lambda)$ and $\rho_\nu \propto \pi_\nu(\Lambda)$ are images of a diagonal matrix. The maximal torus $T \subset \mathrm{U}(d)$ of diagonal unitaries commutes with $\Lambda$, so $[\rho_\mu, U_\mu(t)] = 0$ for all $t \in T$.

By $\mathrm{U}(d)$-covariance, $\mathcal{C}_{\mu \to \nu}(U_\mu(t)\rho_\mu U_\mu(t)^{-1}) = U_\nu(t)\mathcal{C}_{\mu \to \nu}(\rho_\mu)U_\nu(t)^{-1}$. Since $\rho_\mu$ commutes with $U_\mu(t)$, $[\mathcal{C}_{\mu \to \nu}(\rho_\mu), U_\nu(t)] = 0$ for all $t \in T$. Since $\mathcal{H}_\nu$ decomposes into weight spaces with unique phase characters under $T$, $\mathcal{C}_{\mu \to \nu}(\rho_\mu)$ must be block-diagonal in the weight basis. Since $\rho_\nu$ acts as a scalar on each weight space, the two operators commute.

## Dependencies

- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- weight space decomposition
- [[definitions/covariant-channel|U(d)-Covariant Channel]] -- the symmetry requirement

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- simplifies fidelity to a sum over weight blocks
