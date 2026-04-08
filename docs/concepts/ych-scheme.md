# Yang-Chiribella-Hayashi (YCH) Scheme

**Appears in:** Article (Sec. 2.2), Notes (Sec. 3.1)

## Overview

The YCH scheme (2016) solved the qubit compression problem: compressing $\rho^{\otimes n}$ for a qubit state $\rho$ with non-degenerate spectrum. This is the direct precursor to the present project, which generalizes to qudits.

## The Qubit Protocol (Detailed)

For a qubit ($d = 2$) with eigenvalues $p > 1-p > 0$:

### Encoding

1. **Schur transform:** Apply the [[concepts/schur-transform|Schur Transform]] to decompose $(\mathbb{C}^2)^{\otimes n} = \bigoplus_{J} \mathcal{H}_J \otimes \mathcal{M}_J$, where $\mathcal{H}_J$ is the spin-$J$ irrep of $\mathrm{U}(2)$ (dimension $2J+1$, isomorphic to $\mathrm{Sym}^{2J}(\mathbb{C}^2)$) and $\mathcal{M}_J$ is the multiplicity space (an irrep of $S_n$).

2. **Measure the spin $J$:** Perform a non-demolition measurement of the quantum number $J$, which is equivalent to measuring the [[concepts/young-diagrams|Young diagram]] $\lambda = (n/2 + J, n/2 - J)$. This preserves the quantum information within $\mathcal{H}_J$. The probability distribution $q_J$ concentrates sharply around the **typical value** $J^\star = (p - 1/2)(n+1)$, which is the spin corresponding to the typical Young diagram with rows proportional to the spectrum.

3. **Discard the multiplicity register:** The $S_n$ part $\mathcal{M}_J$ is maximally mixed and carries no information about $\rho$, so it can be discarded.

4. **Clone to the typical sector:** Apply [[concepts/werners-cloning-map|Werner's Cloning Map]] $\mathcal{C}_{J \to J^\star}$ to map the state $\rho_{g,J}$ from whatever sector $J$ was measured to the fixed target sector $J^\star$. This is the crucial step: rather than recording the classical outcome $J$ (which would cost $\sim \log n$ bits), we use the covariant cloning map to move all sectors to a single target. For $J \leq J^\star$, this is "cloning up" ($2J$ effective copies to $2J^\star$); for $J > J^\star$, this is partial tracing.

5. **Store:** The output state lives in $\mathcal{H}_{J^\star}$, which has dimension $2J^\star + 1$.

### Decoding

1. **Sample a target spin $K$** from the distribution $q_K$ (which the decoder can compute since $p$ is known).

2. **Clone to the target:** Apply [[concepts/werners-cloning-map|Werner's Cloning Map]] $\mathcal{C}_{J^\star \to K}$ to map from the stored sector to the sampled target sector.

3. **Reconstruct:** Append a fresh maximally mixed multiplicity register $\tau_K$ and apply the inverse Schur transform.

### Why Werner's Cloner Works

The scheme relies on Werner's cloner being **$\mathrm{U}(2)$-covariant**: $\mathcal{C}_{J \to K}(U_J(g) \rho U_J(g)^\dagger) = U_K(g) \mathcal{C}_{J \to K}(\rho) U_K(g)^\dagger$. This means the cloner preserves the rotational structure of the state regardless of the unknown unitary $g$. The cloner does not need to know $g$ -- it treats all orientations equally.

### The Choice of $J^\star$

The target $J^\star = (p - 1/2)(n+1)$ is chosen to maximize $q_J$, i.e., it is the most likely measurement outcome. Since $q_J$ concentrates around $J^\star$ with fluctuations of order $O(\sqrt{n})$, the typical cloning displacement $|J - J^\star|$ is $O(\sqrt{n})$, which is small compared to $J^\star \sim n$. This ensures the cloning fidelity is high.

### The Padding $\xi_n$

In the qudit generalization, one must slightly enlarge the target representation by a "padding" $\xi_n \sim \sqrt{n} \log n$ to ensure all typical sectors can be cloned with high fidelity. This padding is the main source of suboptimal error scaling -- see [[open-questions/error-scaling|Open: Why Does the Error Scale as $\varepsilon \sim n^{-1}$?]].

**Rate:** $\log|M_n| = \frac{1}{2}\log n + \log(2p - 1) + o(1)$

## What Changed for Qudits

The qudit generalization required:
1. Replacing $\mathrm{Sym}^n$ (single-row Young diagrams) with **arbitrary GL$(d)$ irreps** $H_\lambda$
2. Replacing Werner's cloning map with the [[concepts/generalized-cloning-map|Generalized Cloning Map]]
3. Proving the [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] for the generalized cloner (the main technical challenge)

## References

- yang2016optimal: Optimal compression for identically prepared qubit states

## Related

- [[concepts/werners-cloning-map|Werner's Cloning Map]]
- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]

## External References

- [Yang, Chiribella, and Hayashi, "Optimal compression for identically prepared qubit states" (2016)](https://doi.org/10.1103/PhysRevLett.117.090502)
- [Quantum state tomography (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_tomography)
