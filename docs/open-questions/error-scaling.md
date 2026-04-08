# Open: Why Does the Error Scale as $\varepsilon \sim n^{-1}$?

**Source:** Notes, line ~274 (JW comment)
**Status:** Open

## Context

The achievability proof gives compression error $\delta_n = O(n^{-1/4 + \varepsilon})$, which is known to be suboptimal. The authors believe the true scaling should be $\delta_n = O(1/n)$ based on the qubit case (where Werner's cloning map achieves this rate).

## Question

What is the optimal error exponent? Can the generalized cloning map achieve $\delta_n = O(1/n)$ for qudits?

## Current Thinking

The bottleneck is the **padding** $\xi_n \sim \sqrt{n} \log n$. Here is the chain of reasoning:

1. The target representation $\Lambda^\star = n p + \xi_n$ is chosen larger than the typical $\lambda \approx n p$ to ensure that all typical sectors can be cloned *into* it. The padding $\xi_n$ must dominate the typical fluctuations (which are $O(\sqrt{n})$), hence $\xi_n \sim \sqrt{n} \log n$.

2. In the cloning fidelity analysis, the perturbation between the source irrep $H_\mu$ and the target irrep $H_\nu$ (with $\nu = \mu + \omega$) is controlled by the [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]]. The current Davis-Kahan-based bound gives error $O(\sqrt{|\delta| \cdot \|\omega\|/n})$ per weight sector at depth $\delta$.

3. Since $\|\omega\| \sim \xi_n \sim \sqrt{n} \log n$, summing over weight sectors gives the overall error $\delta_n = O(n^{-1/4+\varepsilon})$.

**The key question:** Can one avoid the padding entirely? If one could perform **direct sector-wise cloning** -- cloning within each Schur sector $\lambda$ independently, without first mapping everything to a universal target $\Lambda^\star$ -- then $\|\omega\|$ would be $O(1)$ (just the Schur sector fluctuation), and the error could improve to $O(1/n)$.

The difficulty is that direct sector-wise cloning requires a different target representation for each $\lambda$, which means the memory dimension would depend on the measurement outcome. This seems to require a hybrid classical-quantum memory (storing $\lambda$ classically and the irrep state quantumly), which might not match the formulation of the problem.

An alternative approach: a **direct combinatorial argument on GT patterns** that avoids the Davis-Kahan perturbation theory altogether, directly comparing the GT bases of $H_\mu$ and $H_\nu$ when $\nu = \mu + \omega$ with small $\omega$.

## Related

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]]
- [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]]

## External References

- [Werner, "Optimal cloning of pure states" (1998)](https://doi.org/10.1103/PhysRevA.58.1827)
- [Davis and Kahan, "The rotation of eigenvectors by a perturbation. III" (1970)](https://doi.org/10.1137/0707001)
