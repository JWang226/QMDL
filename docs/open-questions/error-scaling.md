# Open: Error Scaling

**Source:** Notes, line ~274 (JW comment)
**Status:** Open

## Context

The achievability proof gives compression error $\delta_n = O(n^{-1/4 + \varepsilon})$, which is known to be suboptimal. The expected optimal scaling is $\delta_n = O(1/\sqrt{n})$, matching the qubit case established by Yang-Chiribella-Hayashi (YCH).

## Question

What is the optimal error exponent? Can the generalized cloning map achieve $\delta_n = O(1/\sqrt{n})$ for qudits, as in the qubit case?

## Evidence for $1/\sqrt{n}$ Scaling

In the qubit case ($d = 2$), Werner's optimal cloning map achieves error $\delta_n = O(1/\sqrt{n})$. The YCH scheme (Yang-Chiribella-Hayashi 2016) demonstrates this rate explicitly. This suggests the same scaling should hold for general $d$.

## Current Bottleneck

The gap between $n^{-1/4+\varepsilon}$ and $n^{-1/2}$ arises from the **padding** $\xi_n \sim \sqrt{n}\log n$:

1. The target representation $\Lambda^\star = np + \xi_n$ is chosen larger than the typical $\lambda \approx np$ to ensure all typical sectors can be cloned *into* it. The padding $\xi_n$ must dominate the typical fluctuations ($O(\sqrt{n})$), hence $\xi_n \sim \sqrt{n}\log n$.

2. In the cloning fidelity analysis, the perturbation between the source irrep $H_\mu$ and the target irrep $H_\nu$ (with $\nu = \mu + \omega$) is controlled by the [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]]. The current Davis-Kahan-based bound gives error $O(\sqrt{|\delta| \cdot \|\omega\|/n})$ per weight sector at depth $\delta$.

3. Since $\|\omega\| \sim \xi_n \sim \sqrt{n}\log n$, summing over weight sectors gives $\delta_n = O(n^{-1/4+\varepsilon})$.

## Possible Approaches

1. **Direct sector-wise cloning** -- clone within each Schur sector $\lambda$ independently, avoiding the universal target $\Lambda^\star$. This would make $\|\omega\| = O(1)$, potentially improving the error to $O(1/\sqrt{n})$. The difficulty: the memory dimension would depend on the measurement outcome, requiring a hybrid classical-quantum memory.

2. **Direct combinatorial argument on GT patterns** -- avoid the Davis-Kahan perturbation theory altogether, directly comparing the Gelfand-Tsetlin bases of $H_\mu$ and $H_\nu$ when $\nu = \mu + \omega$ with small $\omega$.

## Related

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]]
- [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]]
- [[concepts/ych-scheme|YCH Scheme]]

## External References

- [Yang, Chiribella, and Hayashi, "Optimal compression for identically prepared qubit states" (2016)](https://doi.org/10.1103/PhysRevLett.117.090502)
- [Werner, "Optimal cloning of pure states" (1998)](https://doi.org/10.1103/PhysRevA.58.1827)
- [Davis and Kahan, "The rotation of eigenvectors by a perturbation. III" (1970)](https://doi.org/10.1137/0707001)
