# Conjecture: Free Entropy as Universal QMDL & Programming Extensions

**Source:** Letter, line ~248; Notes, Secs. 7--9
**Status:** Conjectured / Partially established

## Conjecture Statement (from the Letter)

> We conjecture that free entropy describes the quantum minimum description length of **any** operator in quantum mechanics.

More precisely: for any family of operators (density matrices, unitaries, Hermitian operators, or more general objects like CPTP maps), the optimal program size scales as:

$$\log D = \frac{1}{2}\chi_{\mathrm{phy}}(\text{operator}; \varepsilon) + O(1)$$

Free entropy, unlike von Neumann entropy, is defined for **any element of a non-commutative algebra**. This universality of the mathematical definition is conjectured to match a universality of the operational meaning.

## Evidence

The project establishes this for three classes:

### 1. Density Matrices (State Compression) -- Article, Letter
Fully proved with tight $O(1)$ bounds: $|M_n| = \frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1/2}) + O(1)$.

### 2. Unitary Programming -- Notes, Sec. 8
For an $f$-parameter family of unitaries with non-degenerate spectrum: $\log D = \frac{f}{2}\log(1/\varepsilon) + O(1)$.

**Achievability** uses sine states (optimal Bayesian phase estimation, Buzek-Derka-Massar 1999) achieving Heisenberg-limited MSE $\sim 1/D^2$. A coherent variant uses quantum PCA.

**Converse** uses a Holevo information argument.

### 3. Observable Programming -- Notes, Sec. 9
For spectral measurement programming: $\log D = \frac{d^2 \delta(H)}{2}\log(1/\varepsilon) + O(1)$, where $\delta(H)$ is the [[concepts/free-entropy-dimension|Free Entropy Dimension]]. Proved via reduction to unitary programming on the flag manifold.

In all three cases, the leading-order coefficient is $\frac{1}{2}$ times the free entropy dimension.

---

## Open Problems

### Visible Setting Converse (State Programming)
**Notes Sec. 7.** In the visible setting, you know $\rho$ classically and prepare a program state $|\pi_\rho\rangle$. Achievability follows from compression. The **converse is open**: the encoder can use adaptive strategies (different encodings for different $\rho$), breaking the Holevo information argument that works in the blind case. A possible approach: show the decoder can be assumed covariant WLOG.

### Subleading Term for Unitary Programming
For state compression, the $O(1)$ term is $\chi_{\mathrm{reg}}(\rho)$. For unitary programming, only the leading term is established. The authors conjecture it involves the **Kirillov character formula**: the leading order equals the symplectic volume of the coadjoint orbit ([[concepts/kks-theorem|KKS]]), and subleading corrections arise from curvature and the Weyl vector.

### Observable Expectation Converse
For the weaker task of programming $\mathrm{Tr}[H\rho]$ (rather than the full spectral measurement), only achievability is known. The spectral measurement converse uses reduction to unitary estimation, but this breaks down for expectation values -- estimating $\mathrm{Tr}[H\rho]$ does not require knowing the full diagonalizing unitary.

### Further Extensions
- **Quantum channels:** Free entropy can be defined for CPTP maps; the corresponding task is channel programming.
- **Infinite-dimensional connection:** Relating $\chi_{\mathrm{phy}}$ (finite $d$) to Voiculescu's $\chi$ (von Neumann algebra, $d \to \infty$).
- **Multivariate free entropy:** $\chi(a_1, \ldots, a_k)$ should govern joint programming of multiple operators. Free entropy is subadditive, with equality for freely independent operators.

---

## Summary of Open Problems

| Problem | Setting | Status |
|---------|---------|--------|
| Visible converse | State programming | Open |
| Subleading $O(1)$ term | Unitary programming | Open (conjectured: Kirillov formula) |
| Expectation converse | Observable programming | Open |
| Channel programming | CPTP maps | Unexplored |
| Multivariate | Joint programming | Unexplored |

## Related

- [[concepts/free-entropy|Free Entropy]]
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[concepts/free-entropy-dimension|Free Entropy Dimension]]
- [[definitions/regularized-free-entropy|Regularized Free Entropy]]
- [[concepts/kks-theorem|KKS Theorem]]
- [[concepts/holevo-information|Holevo Information]]

## External References

- [Voiculescu, "Free entropy" (survey, 2002)](https://doi.org/10.1112/S0024609301008992)
- [Yang, Renner, and Chiribella, "Optimal universal programming of unitary gates" (2020)](https://doi.org/10.1103/PhysRevLett.125.210501)
- [Kirillov, *Lectures on the Orbit Method* (AMS, 2004)](https://bookstore.ams.org/gsm-64/)
