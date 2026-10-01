# Yang-Chiribella-Hayashi (YCH) Scheme

**Source:** current [[Article]], `sec:review`, `eq:qJ`, `eq:qubitcloning`, and `eq:achievable_qubit`; historical [[Notes]] background.

## Overview

The YCH scheme (2016) solved the qubit compression problem: compressing $\rho^{\otimes n}$ for a qubit state $\rho$ with non-degenerate spectrum. This is the direct precursor to the present project, which generalizes to qudits.

## The Qubit Protocol (Detailed)

For a qubit ($d = 2$) with eigenvalues $p,1-p$ and $1/2<p\le1$, choose $J^\star$ to be an allowed spin nearest the concentration center $(p-1/2)(n+1)$. The allowed spins are $j_{\min},j_{\min}+1,\ldots,n/2$, where $j_{\min}=0$ for even $n$ and $1/2$ for odd $n$. At $p=1$, this gives $J^\star=n/2$.

### Encoding

1. **Schur transform:** Apply the [[concepts/schur-weyl-duality|Schur Transform]] to decompose $(\mathbb{C}^2)^{\otimes n} = \bigoplus_{J} \mathcal{H}_J \otimes \mathcal{M}_J$, where $\mathcal{H}_J$ is the spin-$J$ representation on restriction to $\mathrm{SU}(2)$ (dimension $2J+1$, isomorphic there to $\mathrm{Sym}^{2J}(\mathbb{C}^2)$; the $\mathrm{U}(2)$ determinant twist cancels in conjugation) and $\mathcal{M}_J$ is the multiplicity space (an irrep of $S_n$).

2. **Measure the spin $J$:** Perform a non-demolition measurement of the quantum number $J$, which is equivalent to measuring the [[concepts/young-diagrams|Young diagram]] $\lambda = (n/2 + J, n/2 - J)$. This preserves the quantum information within $\mathcal{H}_J$. The probability distribution $q_J$ concentrates near $(p-1/2)(n+1)$. The chosen $J^\star$ is rounded to the allowed spin lattice; it need not be the exact mode of $q_J$.

3. **Discard the multiplicity register:** The $S_n$ part $\mathcal{M}_J$ is maximally mixed and carries no information about the unknown eigenbasis, so it can be discarded.

4. **Clone to the typical sector:** Apply [[concepts/werners-cloning-map|Werner's Cloning Map]] $\mathcal{C}_{J \to J^\star}$ to map the state $\rho_{g,J}$ from whatever sector $J$ was measured to the fixed target sector $J^\star$. This is the crucial step: rather than recording the classical outcome $J$ (which would cost $\sim \log n$ bits), we use the covariant cloning map to move all sectors to a single target. For $J \leq J^\star$, this is "cloning up" ($2J$ effective copies to $2J^\star$); for $J > J^\star$, this is partial tracing.

5. **Store:** The output state lives in $\mathcal{H}_{J^\star}$, which has dimension $2J^\star + 1$.

### Decoding

1. **Sample a target spin $K$** from the distribution $q_K$ (which the decoder can compute since $p$ is known).

2. **Clone to the target:** Apply [[concepts/werners-cloning-map|Werner's Cloning Map]] $\mathcal{C}_{J^\star \to K}$ to map from the stored sector to the sampled target sector.

3. **Reconstruct:** Append a fresh maximally mixed multiplicity register $\tau_K$ and apply the inverse Schur transform.

### Why Werner's Cloner Works

The scheme relies on Werner's cloner being **$\mathrm{U}(2)$-covariant**: $\mathcal{C}_{J \to K}(U_J(g) \rho U_J(g)^\dagger) = U_K(g) \mathcal{C}_{J \to K}(\rho) U_K(g)^\dagger$. This means the cloner preserves the rotational structure of the state regardless of the unknown unitary $g$. The cloner does not need to know $g$ -- it treats all orientations equally.

### The Choice of $J^\star$

The current Article explicitly uses the nearest allowed spin, not an exact maximizer of $q_J$. For fixed $p>1/2$,

$$J^\star=(p-1/2)(n+1)+O(1).$$

The $O(1)$ rounding changes the log memory dimension by $o(1)$. Concentration near this target makes the displacement small relative to its order-$n$ spin, which is the regime in which the channel approximates the desired representation state.

### The Padding $\xi_n$

In the qudit generalization, one must slightly enlarge the target representation by a "padding" $\xi_n=O(\sqrt{n}\log n)$ to ensure all typical sectors can be cloned with high fidelity. The current direct trace-distance estimate gives $O(\log n/\sqrt n)$ error; see [[open-questions/error-scaling|Error Scaling Beyond the Current Bound]].

**Memory cost:** $|M_n|=\log_2(2J^\star+1)=\log n+\log(2p-1)+o(1)$.

## What Changed for Qudits

The qudit generalization required:
1. Replacing $\mathrm{Sym}^n$ (single-row Young diagrams) with **arbitrary GL$(d)$ irreps** $H_\lambda$
2. Replacing Werner's cloning map with the [[concepts/generalized-cloning-map|Generalized Cloning Map]]
3. Proving the [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]] for the generalized cloner (the main technical challenge)

## References

- yang2016optimal: Optimal compression for identically prepared qubit states

## Related

- [[concepts/werners-cloning-map|Werner's Cloning Map]]
- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]

## External References

- [Yang, Chiribella, and Hayashi, "Optimal compression for identically prepared qubit states" (2016)](https://doi.org/10.1103/PhysRevLett.117.090502)
- [Quantum state tomography (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_tomography)
