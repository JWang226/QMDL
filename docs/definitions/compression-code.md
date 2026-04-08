# Compression Code

**Label:** `eq:error` (Letter)
**Source:** Letter line ~186; Article line ~124; Notes line ~241

## Statement

An $(|M|, \delta)$**-code** for the state $\rho^{\otimes n}$ is a pair of quantum channels:

- **Encoder:** $E: \mathcal{B}((\mathbb{C}^d)^{\otimes n}) \to \mathcal{B}(\mathbb{C}^{|M|})$
- **Decoder:** $D: \mathcal{B}(\mathbb{C}^{|M|}) \to \mathcal{B}((\mathbb{C}^d)^{\otimes n})$

such that the trace-distance error satisfies:

$$\frac{1}{2}\|\rho^{\otimes n} - D \circ E(\rho^{\otimes n})\|_1 \leq \delta$$

Here $|M|$ is the **memory size** (dimension of the compressed system) and $\delta$ is the **error**.

## Intuition

Think of $E$ as a compression algorithm and $D$ as decompression. The code is good if after compress-then-decompress, the state is nearly unchanged. Note: this only requires recovering the **state itself** -- not its purification or entanglement with a reference.

## Key Distinction

This is **not** entanglement-preserving compression (Schumacher). The decoder only needs to recover $\rho^{\otimes n}$, not $|\psi\rangle^{\otimes n}$ for any purification $|\psi\rangle$. This weaker requirement is what makes the rate $O(\log n)$ instead of $O(n)$.

### Why non-entanglement-preserving makes the rate logarithmic

In Schumacher compression, one must preserve entanglement with a reference system, so the compressed space must faithfully encode all $n$ qudits of quantum data -- giving an $O(n)$ rate (the von Neumann entropy $S(\rho)$ per copy). In QMDL compression, we only need to recover the *state itself* $\rho^{\otimes n}$, not its purification. The crucial observation is that $\rho^{\otimes n}$ has permutation symmetry, so by [[concepts/schur-weyl-duality|Schur-Weyl Duality]], it decomposes into sectors labeled by Young diagrams $\lambda$. The information about the eigenbasis of $\rho$ lives entirely in the GL$(d)$ irrep component $\rho_\lambda$, whose dimension is only $\mathrm{poly}(n)$ -- specifically $O(n^{(d^2-d)/2})$ by the [[concepts/weyl-dimension-formula|results/weyl-dimension-asymptotics]]. The multiplicity space $\mathcal{M}_\lambda$ is always maximally mixed and carries no information about the eigenbasis; it only encodes entanglement structure (which we discard). Thus the entire description of $\rho^{\otimes n}$ fits into $O(\log n)$ qubits.

Put differently: the purification of $\rho^{\otimes n}$ carries $O(n)$ qubits of entanglement in the multiplicity registers, but the state *itself* is determined by $O(\log n)$ qubits of eigenbasis data in the GL irrep register.

## Worked Example

**Qubit with $p = 0.7$, $n = 1000$:**

Consider a qubit ($d = 2$) with spectrum $(0.7, 0.3)$. The QMDL formula gives:

$$|M_n| = \frac{1}{2}(d^2 - d)\log n + \sum_{i < j}\log|p_i - p_j| - \sum_{k=0}^{d-1}\log k! + o(1)$$

Substituting $d = 2$, $n = 1000$, $p_1 = 0.7$, $p_2 = 0.3$:

$$|M_n| = \frac{1}{2}(4 - 2)\log_2 1000 + \log_2|0.7 - 0.3| - (\log_2 0! + \log_2 1!)$$

$$= \log_2 1000 + \log_2 0.4 - 0 \approx 9.97 - 1.32 \approx 8.6 \text{ qubits}$$

So the QMDL code compresses $\rho^{\otimes 1000}$ (which lives in a $2^{1000}$-dimensional Hilbert space) into roughly **9 qubits**. This is an exponential compression, from $O(n)$ to $O(\log n)$.

For comparison, Schumacher compression of the same state would require $n \cdot S(\rho) = 1000 \times H(0.7, 0.3) \approx 881$ qubits.

## Connection to Proof Architecture

The compression code is the central object of both the [[results/achievability|Achievability (State Compression)]] and [[results/converse|Converse (State Compression)]] theorems. The encoder applies the Schur transform, measures the Young diagram label $\lambda$, discards the multiplicity register, and uses the [[definitions/generalized-cloning-map-def|Generalized Cloning Map]] $\mathcal{C}_{\lambda \to \Lambda^*}$ to map the GL irrep into a fixed target representation $\Lambda^*$. The converse proves that the memory must be at least $\log \dim \mathcal{H}_\lambda$ for typical $\lambda$, which by the Weyl dimension formula equals the QMDL.

## Used By

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[results/achievability|Achievability (State Compression)]]
- [[results/converse|Converse (State Compression)]]

## External References

- [Shannon's source coding theorem (Wikipedia)](https://en.wikipedia.org/wiki/Shannon%27s_source_coding_theorem)
- [Schumacher, "Quantum coding" (1995)](https://doi.org/10.1103/PhysRevA.51.2738)
