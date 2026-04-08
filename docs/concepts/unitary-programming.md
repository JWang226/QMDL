# Unitary Programming

**Appears in:** [[Notes]] (Sec. 8)

## Intuition

Given an unknown unitary $U$ from a parameterized family $\{U_x\}$, can you store a "program state" $|\pi_U\rangle$ in a quantum memory of dimension $D$ such that a fixed universal processor can later apply $U$ (approximately) to any input? How small can $D$ be?

This is the unitary analogue of [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]: instead of compressing quantum states, you're compressing quantum operations.

## The Programming Task

A universal unitary programmer consists of:
- A **program register** of dimension $D$
- A **processor** $P: \mathcal{H}_{\text{in}} \otimes \mathcal{H}_{\text{prog}} \to \mathcal{H}_{\text{out}}$

such that for each unitary $U_x$ in the family, there exists a program state $|\pi_x\rangle$ with:

$$P(\cdot \otimes |\pi_x\rangle\langle\pi_x|) \approx U_x(\cdot)U_x^\dagger$$

## Main Result

For an $f$-parameter family of unitaries with non-degenerate spectrum:

$$\log D = \frac{f}{2}\log(1/\varepsilon) + O(1)$$

This matches the physical free entropy of the unitary.

## Achievability (Estimation-Based Protocol)

1. Use $D$ copies of the unitary to estimate the parameter $x$
2. Prepare the [[concepts/sine-state|Sine State]] encoding of the estimate: $|P_x\rangle = |\mathrm{sin}_{x_1}\rangle \otimes \cdots \otimes |\mathrm{sin}_{x_f}\rangle$
3. The processor measures each sine state in the Fourier basis and applies the unitary corresponding to the estimate (measure-and-operate)

The sine state achieves MSE $\sim 1/D^2$ (Heisenberg scaling), leading to programming error $\varepsilon \sim 1/D^2$, i.e., $\log D \sim \frac{f}{2}\log(1/\varepsilon)$.

For detailed analysis of the estimation-based protocol and its error bounds, see the [[concepts/sine-state|Sine State]] and [[results/estimation-programming-lemma|Estimation-Programming Lemma]] pages.

### A Coherent Protocol (using qPCA)

There is also a **coherent** (non-measure-and-operate) protocol: to program $e^{-i\rho t}$, prepare $\mathcal{E}(\rho^{\otimes m})$ as the program (using the optimal state compression encoder $\mathcal{E}$), then have the processor decode to recover $\rho^{\otimes m}$ and apply **quantum principal component analysis** (qPCA) to realize $\rho^{\otimes m} \to e^{-i\rho t}$. The qPCA error is $O(t^2/m)$, requiring $m \sim 1/\varepsilon$, and the program size is $(f/2)\log m + O(1)$ -- matching the same leading-order rate.

## Converse

Uses a Holevo information argument: the program state cannot encode more than $\log D$ bits of classical information, bounding how precisely the unitary parameter can be recovered.

## Open Question

The $O(1)$ subleading term (analogous to [[definitions/regularized-free-entropy|Regularized Free Entropy]] for states) is not yet determined. The authors conjecture it involves the Kirillov character formula.

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- state compression analogue
- [[concepts/observable-programming|Observable Programming]] -- observable analogue
- [[concepts/free-entropy|Free Entropy]] -- governs the compression rate
- [[concepts/sine-state|Sine State]] -- the key ingredient in the achievability proof
- [[results/estimation-programming-lemma|Estimation-Programming Lemma]] -- converts estimation error to programming error
- [[open-questions/unitary-subleading|Open: Subleading Term for Unitary Programming]] -- the $O(1)$ term is open

## External References

- M. A. Nielsen and I. L. Chuang, "Programmable quantum gate arrays," *Phys. Rev. Lett.* 79, 321--324 (1997)
- [Yang, Renner, and Chiribella, "Optimal universal programming of unitary gates" (2020)](https://doi.org/10.1103/PhysRevLett.125.210501)
- [Quantum programming (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_programming)
