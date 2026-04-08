# State Programming (Visible Setting)

**Appears in:** Notes (Sec. 7)

## Overview

In the **visible setting**, you want to prepare a program state $|\pi_\rho\rangle$ of dimension $D$ such that a fixed universal processor outputs $\rho^{\otimes n}$ approximately:

$$P(|\pi_\rho\rangle\langle\pi_\rho| \otimes |\phi\rangle\langle\phi|) \approx \rho^{\otimes n}$$

This is the "programming" formulation of state compression, dual to the "compression" formulation of [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]].

## Relation to Compression: A Crucial Distinction

The programming and compression tasks sound similar but differ in a subtle, important way:

- **Compression** (blind): You are *handed* the physical state $\rho^{\otimes n}$ and must encode it into a smaller quantum memory. The encoder is a single fixed channel $\mathcal{E}$ that works for all $\rho$ (or at least for the Schur sector). You have no side information about which $\rho$ you received.

- **Programming** (visible): You *know* $\rho$ classically (you know its eigenvalues and eigenvectors) and must *prepare from scratch* a program state $|\pi_\rho\rangle$ of dimension $D$. You never touch $\rho^{\otimes n}$ directly. A fixed universal processor $\mathcal{D}$ then takes $|\pi_\rho\rangle$ and outputs an approximation to $\rho^{\otimes n}$.

The key difference is the starting point:

| | Input | What you do |
|---|---|---|
| **Compression** | Physical state $\rho^{\otimes n}$ | Shrink it |
| **Programming** | Classical description of $\rho$ | Build a program from scratch |

**Why achievability is easy:** If the blind encoder can compress $\rho^{\otimes n}$ into $\log D$ qubits, then someone who *knows* $\rho$ can certainly prepare the compressed state directly -- they can simulate the encoding in their head and just prepare the output. So programming is at least as easy as compression.

**Why the converse is hard:** In the programming setting, the encoder knows $\rho$ classically and could in principle use *adaptive strategies* that exploit this knowledge in ways not available to a blind compressor. For instance, the encoder could choose entirely different program states for different $\rho$, with no requirement that the mapping $\rho \mapsto |\pi_\rho\rangle$ comes from a single quantum channel. This extra freedom makes it harder to prove a matching lower bound. See [[open-questions/visible-converse|Open: Visible Setting Converse]] for the current status.

## Open Question

The converse for the visible setting is **open** -- see [[open-questions/visible-converse|Open: Visible Setting Converse]].

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[concepts/unitary-programming|Unitary Programming]]
- [[open-questions/visible-converse|Open: Visible Setting Converse]]

## External References

- [Quantum state tomography (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_tomography)
- [Yang, Chiribella, and Hayashi, "Optimal compression for identically prepared qubit states" (2016)](https://arxiv.org/abs/1507.08171)
- M. Hayashi, *Quantum Information Theory: Mathematical Foundation*, Graduate Texts in Physics, Springer (2017)
