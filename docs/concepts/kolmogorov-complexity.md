# Kolmogorov Complexity and Quantum Kolmogorov Complexity

**Appears in:** [[Letter]] (Discussion), [[Article]] (Sec. 1)

## Classical Kolmogorov Complexity

The **Kolmogorov complexity** $K(x)$ of a string $x$ is the length of the shortest program $p$ such that a universal Turing machine $U$ outputs $x$ on input $p$:

$$K(x) = \min\{|p| : U(p) = x\}$$

**Key properties:**
- **Invariance:** The choice of universal Turing machine changes $K(x)$ by at most an additive constant.
- **Upper bound:** $K(x) \leq |x| + c$ -- no string is much harder to describe than to write down literally.
- **Incompressibility:** Most strings of length $n$ satisfy $K(x) \geq n$ (algorithmically random).
- **Incomputability:** $K(x)$ is not computable. It can be approximated from above but not from below.

**Relevance:** A classical repetitive string $s^n$ has $K(s^n) = \log n + O(1)$ -- you need $O(1)$ bits for the repeating unit and $\log n$ bits for the length. The QMDL result is structurally analogous.

## Rissanen's Minimum Description Length

Rissanen (1978) introduced the **Minimum Description Length (MDL) principle** as a practical, computable restriction of the Kolmogorov complexity idea. Instead of searching over all programs (incomputable), MDL restricts to descriptions corresponding to specified probability models, making the optimization computable.

The total description length is: description of the model + description of the data given the model.

The relationship:
- **Kolmogorov complexity** is the theoretically ideal but incomputable measure of descriptive complexity.
- **MDL** is its computable operational counterpart, restricted to a model class.

## Quantum Kolmogorov Complexity (QKC)

Several definitions of QKC have been proposed:

**Berthiaume, van Dam, Laplante (2001):** QKC of a quantum state $|\psi\rangle$ is the length of the shortest quantum input to a universal quantum Turing machine that outputs $|\psi\rangle$ with high fidelity. Their Theorem 7 shows that $n$ copies of a pure qubit state have QKC $\sim \log n$.

**Gacs (2001):** Defines complexity via a universal semicomputable density matrix; the complexity is an *operator* (the negative logarithm of this universal density matrix). Theorem 15 gives a result about the complexity of copies of pure states.

**Mueller (2007):** Provides rigorous proofs of basic QKC properties: invariance, incompressibility, agreement with classical KC for classical strings, and connection to von Neumann entropy for ergodic sources.

All definitions of QKC inherit the **incomputability** of classical Kolmogorov complexity.

## QMDL as Quantum MDL

The [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] is the quantum analogue of Rissanen's MDL -- a computable, operationally defined quantity:

| | Classical | Quantum |
|---|---|---|
| **Incomputable ideal** | Kolmogorov complexity $K(x)$ | Quantum Kolmogorov complexity $\mathrm{QK}(|\psi\rangle)$ |
| **Computable operational** | Rissanen's MDL | QMDL |
| **Governs i.i.d. compression** | Shannon entropy $H$ | Free entropy $\chi$ |

The Letter interprets the QMDL of $\rho^{\otimes n}$ as the quantum Kolmogorov complexity of the family $\{(U\rho_0 U^\dagger)^{\otimes n}\}_{U \in \mathrm{U}(d)}$ -- the exact definition of QKC does not matter for this interpretation (Mueller 2007).

The structural parallel:
- Classical: $K(s^n) = \log n + O(1)$ for a repetitive string
- Quantum: $|M_n| = \frac{1}{2}r(2d-r-1)\log n + O(1)$ for $\rho^{\otimes n}$

Both scale as $O(\log n)$, but the quantum case has $\frac{1}{2}\log n$ per degree of freedom due to the geometric quantization factor ([[concepts/kks-theorem|KKS Theorem]]).

## Two Distinct "Kolmogorov" Concepts

This project uses "Kolmogorov" in two distinct senses:
1. **Kolmogorov (algorithmic) complexity** -- the length of the shortest program producing an object (this page)
2. **Kolmogorov $\varepsilon$-entropy (metric entropy)** -- the covering number of a set at resolution $\varepsilon$, used to define [[concepts/physical-free-entropy|Physical Free Entropy]]. See [[concepts/covering-numbers|Covering Numbers]].

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[concepts/covering-numbers|Covering Numbers]] -- Kolmogorov $\varepsilon$-entropy (a different "Kolmogorov")
- [[concepts/kks-theorem|KKS Theorem]] -- the factor-of-1/2 quantization

## References

- rissanen1978modeling: Rissanen, "Modeling by shortest data description" (1978)
- Berthiaume_2001: Berthiaume, van Dam, Laplante, "Quantum Kolmogorov complexity" (2001)
- G_cs_2001: Gacs, "Quantum algorithmic entropy" (2001)
- mueller2007: Mueller, "Quantum Kolmogorov complexity and the quantum Turing machine" (2007)

## External References

- [Kolmogorov complexity (Wikipedia)](https://en.wikipedia.org/wiki/Kolmogorov_complexity)
- [Minimum description length (Wikipedia)](https://en.wikipedia.org/wiki/Minimum_description_length)
- M. Li and P. Vitanyi, *An Introduction to Kolmogorov Complexity and Its Applications*, Springer (2008)
