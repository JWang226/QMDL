# Principal Angles (Lemma 4)

**Label:** `lem:principle_angles`
**Source:** Article line ~1095 (stated), ~2511 (proved)

## Statement

For projectors $P, Q$ with $r = \min(\mathrm{rank}\, P, \mathrm{rank}\, Q)$:

$$\mathrm{Tr}\sqrt{PQP} = \sum_{i=1}^r \cos(\theta_i)$$

where $\theta_i$ are the principal angles between $\mathrm{Im}(P)$ and $\mathrm{Im}(Q)$.

## Intuition

The fidelity between two subspaces (as measured by $\mathrm{Tr}\sqrt{PQP}$) equals the sum of cosines of the angles between them. This connects an algebraic quantity (trace of a matrix square root) to a geometric one (angles between subspaces).

## Proof Sketch

Let $U, V$ have orthonormal columns spanning $\mathrm{Im}(P)$ and $\mathrm{Im}(Q)$. Then $PQP = U(U^\dagger V)(U^\dagger V)^\dagger U^\dagger$. The nonzero eigenvalues of $PQP$ equal the squared singular values $\sigma_i^2 = \cos^2\theta_i$ of $M = U^\dagger V$. Taking the positive square root gives eigenvalues $\cos\theta_i$, and the trace sums them.

## Dependencies

- Linear algebra (singular value decomposition)

## Used By

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- the block fidelity $F_{\mathrm{block}}(\delta) = \sqrt{d_\mu/d_\nu} \sum_i \cos\theta_i$ where $\theta_i$ are the principal angles between uncoupled and coupled weight subspaces

## Key Equations

$$F_{\mathrm{block}}(\delta) = \sqrt{d_\mu/d_\nu} \, \mathrm{Tr}\sqrt{\widetilde{\Pi}_{\nu-\delta} \Pi_{\mu-\delta}^{(\omega)} \widetilde{\Pi}_{\nu-\delta}}$$
