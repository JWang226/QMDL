# Schumacher Compression

**Appears in:** [[Letter]], [[Article]] (Sec. 1)

## Overview

Schumacher compression (1995) is the quantum analogue of Shannon source coding. Given $n$ copies of a quantum state $\rho$, compress into $\sim nS(\rho)$ qubits while preserving the state **and all its entanglement** with any reference system.

## Comparison with QMDL

| | Schumacher | QMDL |
|---|---|---|
| **Preserves** | State + purification | State only |
| **Rate** | $nS(\rho)$ (linear in $n$) | $O(\log n)$ (logarithmic!) |
| **Entropy notion** | Von Neumann entropy $S(\rho)$ | [[concepts/free-entropy|Free Entropy]] $\chi(\rho)$ |
| **What's stored** | Quantum information | Description of eigenbasis |
| **Regime** | $n \to \infty$ | $n \to \infty$, spectrum known |

## Why the Dramatic Difference?

Schumacher compression must preserve the full quantum state including its entanglement with any reference. This requires storing $nS(\rho)$ qubits worth of quantum information -- the purification carries genuine quantum correlations that cannot be compressed below the von Neumann entropy rate.

QMDL only needs to recover the state itself, without preserving entanglement with a reference. Since the spectrum is known, only the eigenbasis (a point on a [[concepts/flag-manifold|Flag Manifold]]) needs to be stored. This is a **continuous parameter** that can be specified to precision $\sim 1/\sqrt{n}$ using $O(\log n)$ qubits.

A vivid example: for a pure state $|\psi\rangle$, the von Neumann entropy is $S = 0$, so Schumacher compression is trivial (the source deterministically produces $|\psi\rangle$). But for someone who does *not* know $|\psi\rangle$, it still takes $(d-1)\log n + O(1)$ qubits of QMDL to store a description of $|\psi\rangle^{\otimes n}$. The free entropy captures this descriptive cost that von Neumann entropy completely misses.

## The Two Routes to Non-Commutative Entropy

The Letter frames the relationship between Schumacher and QMDL as two fundamentally different non-commutative generalizations of Shannon entropy, starting from two different expressions for $H(p)$.

### Route 1: Von Neumann's route (typical subspaces)

Start from the closed-form formula for Shannon entropy and replace probabilities with density operators:

$$H(p) = -\sum_i p_i \log p_i \quad \longrightarrow \quad S(\rho) = -\mathrm{Tr}[\rho\log\rho]$$

The operational content comes from typical *subspaces*. The von Neumann entropy admits a Boltzmann-type expression:

$$S(\rho) = \inf_\varepsilon \lim_{N \to \infty} \frac{1}{N}\log\left(\min_V \dim\{V \subset \mathcal{H}^{\otimes N} : \mathrm{Tr}(\rho^{\otimes N}\Pi_V) \geq 1 - \varepsilon\}\right)$$

Here $V$ is a subspace that captures at least $1-\varepsilon$ of the weight of $\rho^{\otimes N}$, and the minimum is attained by the subspace spanned by the largest eigenvectors (the "typical subspace"). The logical chain is:

$$\text{typical sequences} \to \text{typical subspaces} \to \text{von Neumann entropy} \to \text{Schumacher compression}$$

The independence structure is **tensor independence**: $\rho^{\otimes N}$ is a tensor product, the typical subspace decomposes as a tensor product of eigenspaces, and $S(\rho)$ is additive under tensor products.

### Route 2: Voiculescu's route (typical matrices)

Start from the Boltzmann expression for Shannon entropy and replace strings with matrices:

$$H(p) = \inf_\varepsilon \lim_{N \to \infty} \frac{1}{N}\log\#\{x^N : \|p_{x^N} - p\| \leq \varepsilon\} \quad \longrightarrow \quad \chi(a) = \inf_{m,\varepsilon}\lim_{N \to \infty}\left[\frac{1}{2}\log N + \frac{1}{N^2}\log\mathrm{Vol}(\Gamma(a;m,\varepsilon,N))\right]$$

Instead of counting typical strings, we measure the volume of typical *matrices* -- those $N \times N$ self-adjoint matrices $X_N$ whose moments approximate those of $a$. The logical chain is:

$$\text{typical strings} \to \text{typical matrices} \to \text{free entropy} \to \text{QMDL}$$

The independence structure is **free independence**: the eigenbasis and eigenvalues of a Haar-random matrix are freely independent in the large-$N$ limit, and $\chi$ is additive under free products.

### Why these are fundamentally different

The two routes differ not just quantitatively but structurally:

- **Tensor vs. free independence.** Von Neumann entropy is additive under $\otimes$ (tensor product), while free entropy is additive under $*$ (free product). These are genuinely different algebraic operations.

- **What gets quantized.** Route 1 quantizes the probability density function $p(x)$ by promoting it to a density operator $\rho$. Route 2 quantizes the random variable $X$ itself by promoting it to a random matrix $X_N$. The first changes what carries the information; the second changes what the information is about.

- **Linear vs. logarithmic scaling.** Schumacher compression requires $O(n)$ qubits because it stores genuine quantum information (entanglement). QMDL requires $O(\log n)$ qubits because it stores a classical parameter (the eigenbasis) to precision $O(n^{-1/2})$.

- **Information content.** Von Neumann entropy measures how much entanglement the state carries. Free entropy measures how complex the state's eigenbasis is -- a geometric property of the unitary orbit, completely invisible to von Neumann entropy.

## References

- schumacher1995quantum: Original Schumacher compression paper
- jozsa1998universal: Universal quantum compression

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- the QMDL task
- [[concepts/free-entropy|Free Entropy]] -- the entropy governing QMDL
- [[concepts/physical-free-entropy|Physical Free Entropy]] -- the finite-dimensional version
- [[Von Neumann Entropy]] -- the entropy governing Schumacher compression

## External References

- [Quantum data compression (Wikipedia)](https://en.wikipedia.org/wiki/Schumacher%27s_noiseless_quantum_coding_theorem)
- [Von Neumann entropy (Wikipedia)](https://en.wikipedia.org/wiki/Von_Neumann_entropy)
- [Schumacher, "Quantum coding" (1995)](https://doi.org/10.1103/PhysRevA.51.2738)
- M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge University Press (2000)
