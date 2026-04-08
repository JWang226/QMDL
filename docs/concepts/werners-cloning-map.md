# Werner's Cloning Map

**Appears in:** Article (Sec. 2.2, Sec. 3.2.1), Notes (Sec. 3.1)

## Intuition

Werner's cloning map is the optimal way to "clone" a quantum state from $n$ copies to $m > n$ copies, when the states live in symmetric subspaces. It is the **qubit special case** of the [[concepts/generalized-cloning-map|Generalized Cloning Map]].

## Formal Description

For qubits ($d = 2$), the symmetric subspace $\mathrm{Sym}^n(\mathbb{C}^2)$ has dimension $n+1$. Werner's cloning map $W_{n \to m}: \mathcal{B}(\mathrm{Sym}^n) \to \mathcal{B}(\mathrm{Sym}^m)$ is defined by:

$$W_{n \to m}(\sigma) = \frac{n+1}{m+1} P_{\mathrm{Sym}^m} (\sigma \otimes I_{m-n}) P_{\mathrm{Sym}^m}$$

where $P_{\mathrm{Sym}^m}$ is the projector onto $\mathrm{Sym}^m(\mathbb{C}^2)$.

## Key Properties

1. **$U(d)$-covariant**: commutes with the $U(d)$ action, i.e., $W_{n \to m}(U^{\otimes n} \rho (U^\dagger)^{\otimes n}) = U^{\otimes m} W_{n \to m}(\rho) (U^\dagger)^{\otimes m}$
2. **Optimal**: achieves the best fidelity for $1 \to m$ cloning of pure states (Keyl-Werner 1999)
3. **Fidelity for pure states**: For cloning a single pure qubit state $|\psi\rangle$ from $n$ copies to $m$ copies:

$$F = \frac{n+1}{m+1}$$

This is a remarkably clean formula. When $m = n$, fidelity is 1 (no cloning needed). As $m \to \infty$ with $n$ fixed, fidelity $\to 0$ (you cannot create infinitely many clones from finite information). Keyl and Werner proved this is **optimal**: no cloning map, covariant or not, can achieve higher fidelity for the worst-case pure state input.

**Intuition for the formula:** The symmetric subspace $\mathrm{Sym}^n(\mathbb{C}^2)$ has dimension $n+1$. Werner's cloner embeds the $n$-copy symmetric subspace into the $m$-copy one by tensoring with the identity and projecting. The dimension ratio $(n+1)/(m+1)$ is the trace-preserving normalization factor, and it directly gives the fidelity because the overlap between the projected state and the target is controlled by this ratio.

## Role in the Project

The Yang-Chiribella-Hayashi (YCH) qubit compression scheme uses Werner's cloning map to move states between different symmetric subspaces. The [[concepts/generalized-cloning-map|Generalized Cloning Map]] extends this from $\mathrm{Sym}^n$ (single-row Young diagrams) to arbitrary Young diagrams, enabling the qudit generalization.

## References

- werner1998optimal: Original paper by Werner (1998)
- keyl1999optimal: Keyl-Werner extension (1999)

## Related

- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- the qudit generalization
- [[concepts/ych-scheme|YCH Scheme]] -- uses Werner's cloner for qubit compression

## External References

- [Quantum cloning (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_cloning)
- [Werner, "Optimal cloning of pure states, testing single clones" (1998)](https://arxiv.org/abs/quant-ph/9804001)
- [Scarani, Iblisdir, Gisin, and Acin, "Quantum cloning" (2005)](https://arxiv.org/abs/quant-ph/0511088)
- [Keyl and Werner, "Optimal cloning of pure states, judging single clones" (1999)](https://arxiv.org/abs/quant-ph/9910053)
