# Reverse Cloner (Proposition 2)

**Label:** `prop:reverse`
**Source:** Article line ~392 (stated), ~2027 (proved)

## Statement

The Petz recovery map of $\mathcal{C}_{\mu \to \nu}$ with respect to $\sigma_\mu = I/d_\mu$ equals the reverse cloning map:

$$\mathcal{C}_{\nu \to \mu}(X) = \frac{d_\nu}{d_\mu} \mathcal{C}_{\mu \to \nu}^\dagger(X)$$

## Intuition

The generalized cloning map is self-dual up to normalization: its Petz recovery map (the "optimal reversal") is just the cloning map in the opposite direction $\nu \to \mu$. In the Stinespring picture, the reverse cloner $\mathcal{C}_{\nu \to \mu}(X) = \mathrm{Tr}_\omega(VXV^\dagger)$ is simply a partial trace.

## Proof Sketch

**Step 1.** The cloning map sends maximally mixed to maximally mixed: by covariance and Schur's lemma, $\mathcal{C}_{\mu \to \nu}(\sigma_\mu) = \sigma_\nu$. So the Petz map simplifies to $\mathcal{R}(X) = (d_\nu/d_\mu) \mathcal{C}_{\mu \to \nu}^\dagger(X)$.

**Step 2.** The Kraus operators $\{K_a\}$ of $\mathcal{C}_{\mu \to \nu}$ span a space $\mathsf{K}_\omega \subset \mathrm{Hom}(\mathcal{H}_\mu, \mathcal{H}_\nu)$ carrying the irrep $\omega$. The adjoint $K \mapsto K^\dagger$ gives an antiunitary intertwiner, so $\{K_a^\dagger\}$ spans a space carrying the dual irrep $\omega^*$, which is exactly the PRV component for the reversed pair. The Choi operator matches $\mathcal{C}_{\nu \to \mu}$.

## Dependencies

- [[concepts/petz-recovery-map|Petz Recovery Map]]
- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[concepts/prv-component|PRV Component]]

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- Step 9: the reverse-direction argument via partial trace
