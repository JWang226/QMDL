# Compression Code

**Label:** `eq:error` in both the current [[Letter]] and [[Article]].
**Source:** [Letter compression task](https://github.com/JWang226/QMDL/blob/main/letter.tex#L183) and [Article introduction](https://github.com/JWang226/QMDL/blob/main/article.tex#L76). The earlier [[Notes]] use their own version.

## Statement

Let $M$ be the sole retained memory, including any retained classical register. Put $m=\dim M$ and $|M|=\log_2 m$, as in the current Article. An $(|M|,\delta)$-code consists of CPTP maps

$$\mathcal E:\mathcal B((\mathbb C^d)^{\otimes n})\to\mathcal B(M),\qquad
\mathcal D:\mathcal B(M)\to\mathcal B((\mathbb C^d)^{\otimes n})$$

that may depend on the known spectrum and $n$, but not on the unknown orbit parameter $g$, and satisfy

$$\sup_{g\in U(d)}\frac12\|\rho_g^{\otimes n}-\mathcal D\mathcal E(\rho_g^{\otimes n})\|_1\le\delta.$$

The distinction between $m$ and $|M|$ matters: the former is a dimension, the latter is the logarithmic memory cost. Lean's `memory n : ℕ` represents the dimension, with `Real.logb 2 (memory n)` the cost. The final converse also allows merely vanishing Haar-average error.

## Intuition

Think of $E$ as a compression algorithm and $D$ as decompression. The code is good if after compress-then-decompress, the state is nearly unchanged. Note: this only requires recovering the **state itself** -- not its purification or entanglement with a reference.

## Key Distinction

This is **not** entanglement-preserving compression (Schumacher). The decoder only needs to recover $\rho^{\otimes n}$, not $|\psi\rangle^{\otimes n}$ for any purification $|\psi\rangle$. For a mixed source, this weaker requirement permits logarithmic memory instead of the extensive $nS(ho)$ cost. For pure states there is no purification to preserve; the distinction is that the QMDL encoder knows only the spectrum, while the usual known-source Schumacher task can regenerate a known pure state.

### Why non-entanglement-preserving makes the rate logarithmic

In Schumacher compression, one must preserve entanglement with a reference system, so the compressed space must faithfully encode all $n$ qudits of quantum data -- giving an $O(n)$ rate (the von Neumann entropy $S(\rho)$ per copy). In QMDL compression, we only need to recover the *state itself* $\rho^{\otimes n}$, not its purification. The crucial observation is that $\rho^{\otimes n}$ has permutation symmetry, so by [[concepts/schur-weyl-duality|Schur-Weyl Duality]], it decomposes into sectors labeled by Young diagrams $\lambda$. The information about the eigenbasis of $\rho$ lives entirely in the GL$(d)$ irrep component $\rho_\lambda$, whose dimension is only $\mathrm{poly}(n)$ -- specifically $O(n^{(d^2-d)/2})$ by the [[concepts/weyl-dimension-formula|Weyl dimension formula]]. The multiplicity space $\mathcal{M}_\lambda$ is always maximally mixed and carries no information about the eigenbasis; its known maximally mixed state can be re-prepared. Thus the entire description of $\rho^{\otimes n}$ fits into $O(\log n)$ qubits.

Put differently: the purification of $\rho^{\otimes n}$ carries $O(n)$ qubits of entanglement in the multiplicity registers, but the state *itself* is determined by $O(\log n)$ qubits of eigenbasis data in the GL irrep register.

## Worked Example

**Qubit with $p = 0.7$, $n = 1000$:**

Consider a qubit ($d = 2$) with spectrum $(0.7, 0.3)$. The QMDL formula gives:

$$|M_n| = \frac{1}{2}(d^2 - d)\log n + \sum_{i < j}\log|p_i - p_j| - \sum_{k=0}^{d-1}\log k! + o(1)$$

Substituting $d = 2$, $n = 1000$, $p_1 = 0.7$, $p_2 = 0.3$:

$$|M_n| = \frac{1}{2}(4 - 2)\log_2 1000 + \log_2|0.7 - 0.3| - (\log_2 0! + \log_2 1!)$$

$$= \log_2 1000 + \log_2 0.4 - 0 \approx 9.97 - 1.32 \approx 8.6 \text{ qubits}$$

The asymptotic expression suggests about **9 qubits**. It is not a finite-$n$ guarantee of that exact memory/error pair: the constructed padded target can be larger at $n=1000$.

For comparison, Schumacher compression of the same state would require $n \cdot S(\rho) = 1000 \times H(0.7, 0.3) \approx 881$ qubits.

## Connection to Proof Architecture

The compression code is the central object of both the [[results/achievability|Achievability (State Compression)]] and [[results/converse|Converse (State Compression)]] theorems. The encoder applies the Schur transform, measures the Young diagram label $\lambda$, discards the multiplicity register, and uses the [[definitions/generalized-cloning-map-def|Generalized Cloning Map]] $\mathcal{C}_{\lambda \to \Lambda^*}$ to map the GL irrep into a fixed target representation $\Lambda^*$. The converse transfers any physical code to the padded orbit and applies the quantitative irreducible-orbit memory bound. `Theorem1Complete` proves both final results for actual CPTP maps, with no assumed protocol or transfer-error estimate. See [[proof-structure]].

## Used By

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[results/achievability|Achievability (State Compression)]]
- [[results/converse|Converse (State Compression)]]

## External References

- [Shannon's source coding theorem (Wikipedia)](https://en.wikipedia.org/wiki/Shannon%27s_source_coding_theorem)
- [Schumacher, "Quantum coding" (1995)](https://doi.org/10.1103/PhysRevA.51.2738)
