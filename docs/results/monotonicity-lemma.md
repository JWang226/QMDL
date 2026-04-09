# Monotonicity (Lemma 5)

**Label:** `lem:monotonicity`
**Source:** Article line ~1175 (stated), ~2545 (proved)

## Statement

For a quantum channel $\mathcal{N}$ with Kraus operator $K$ and $\rho' = K\eta K^\dagger$ (unnormalized), for any density operator $\sigma$:

$$F(\rho', \sigma) \leq F(\mathcal{N}(\eta), \sigma)$$

## Intuition

The fidelity can only increase (or stay the same) when you include all Kraus branches of a channel rather than just one. Restricting to a single Kraus operator gives a lower bound on the full-channel fidelity.

## Proof Sketch

Write $\mathcal{N}(\eta) = K\eta K^\dagger + \sum_i L_i \eta L_i^\dagger = \rho' + \rho_{\mathrm{rem}}$. Since $\rho_{\mathrm{rem}} \geq 0$, we have $\mathcal{N}(\eta) \geq \rho'$. Conjugating by $\sqrt{\sigma}$ and applying the Lowner-Heinz theorem ($\sqrt{x}$ is operator monotone) gives $\sqrt{\sqrt{\sigma}\,\mathcal{N}(\eta)\,\sqrt{\sigma}} \geq \sqrt{\sqrt{\sigma}\,\rho'\,\sqrt{\sigma}}$. Taking traces yields the result.

## Dependencies

- Lowner-Heinz theorem (operator monotonicity of $\sqrt{x}$)

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- Step 2: reduces from the full channel $\widetilde{\mathcal{C}}_{\mu \to \nu}$ to the single highest-weight Kraus branch $\mathcal{K}_\omega$, which is easier to analyze because $|\omega\rangle$ is annihilated by raising operators
