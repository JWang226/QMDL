# Open: Programming Extensions (Notes, Sec. 7--9)

**Source:** Notes (Free.tex), Sections 7--9
**Status:** Open / Partially developed

The Notes develop three extensions of the QMDL framework beyond state compression. These are not covered in the Article or Letter and contain several open questions. This page summarizes the key ideas and records the open problems.

---

## 1. State Programming (Visible Setting)

**Notes Sec. 7.** In the **visible setting**, you know $\rho$ classically and must prepare a program state $|\pi_\rho\rangle$ of dimension $D$ such that a fixed universal processor outputs $\rho^{\otimes n}$ approximately. This is dual to the blind compression formulation of [[concepts/quantum-minimum-description-length|QMDL]].

**Achievability** follows from the compression result: if the blind encoder can compress $\rho^{\otimes n}$ into $\log D$ qubits, someone who knows $\rho$ can prepare the compressed state directly.

**Open: Converse.** The converse is open. In the blind setting the encoder is a single CPTP map $\mathcal{E}$, and Schur's lemma constrains it. In the visible setting the mapping $\rho \mapsto |\pi_\rho\rangle$ can be an arbitrary function exploiting classical knowledge of $\rho$. Proving that such adaptive strategies cannot beat blind compression is the core difficulty. A possible approach (suggested in the Notes): show the decoder $\mathcal{D}$ can be assumed covariant WLOG by averaging over the unitary group, then use Schur's lemma to constrain the program states.

---

## 2. Unitary Programming

**Notes Sec. 8.** Given an unknown unitary $U_x$ from an $f$-parameter family with non-degenerate spectrum, store a program state $|\pi_U\rangle$ of dimension $D$ such that a fixed universal processor approximately implements $U_x$.

**Main result (Notes):**

$$\log D = \frac{f}{2}\log(1/\varepsilon) + O(1)$$

**Achievability** uses an estimation-based protocol: estimate the parameter $x$ using $D$ copies, prepare a **sine state** $|\mathrm{sin}_x\rangle$ (optimal Bayesian phase estimation state from Buzek-Derka-Massar 1999) encoding the estimate, then measure and operate. The sine state achieves Heisenberg-limited MSE $\sim 1/D^2$, giving programming error $\varepsilon \sim 1/D^2$. A coherent (non-measure-and-operate) variant uses quantum PCA.

**Converse** uses a Holevo information argument bounding how precisely the unitary parameter can be recovered from the program state.

**Open: Subleading term.** For state compression, the $O(1)$ subleading term is precisely $\chi_{\mathrm{reg}}(\rho)$ (the [[definitions/regularized-free-entropy|Regularized Free Entropy]]). For unitary programming, only the leading term is established. The authors conjecture the $O(1)$ term involves the **Kirillov character formula**: the leading order of $\dim H_\lambda$ equals the symplectic volume of the coadjoint orbit (the [[concepts/kks-theorem|KKS]] content), and subleading corrections arise from curvature and the Weyl vector. Establishing this would complete the parallel between state compression and unitary programming.

---

## 3. Observable Programming

**Notes Sec. 9.** Given a Hermitian observable $H$ with distinct eigenvalues of multiplicities $g_1, \ldots, g_m$, program either its spectral measurement or its expectation value.

### Spectral Measurement Programming

$$\log D = \frac{d^2 \cdot \delta(H)}{2}\log(1/\varepsilon) + O(1)$$

where $\delta(H) = 1 - \sum_a g_a^2/d^2$ is the [[concepts/free-entropy-dimension|Free Entropy Dimension]]. Achievability and converse are both established via reduction to unitary programming on the flag manifold $U(d)/(U(g_1) \times \cdots \times U(g_m))$.

### Expectation Value Programming

Program only the ability to estimate $\mathrm{Tr}[H\rho]$ for any input $\rho$. Achievability follows from spectral measurement programming.

**Open: Converse.** The spectral measurement converse uses a reduction to unitary estimation on the flag manifold: programming $\{P_i\}$ implicitly encodes the diagonalizing unitary $U$. For expectation values, this reduction breaks down -- estimating $\mathrm{Tr}[H\rho]$ does not require knowing the full unitary $U$. A fundamentally new argument (e.g., information-theoretic) would be needed to show the same rate is a lower bound for this weaker task.

---

## Summary of Open Problems

| Problem | Setting | Status |
|---------|---------|--------|
| Visible converse | State programming | Open |
| Subleading $O(1)$ term | Unitary programming | Open (conjectured: Kirillov formula) |
| Expectation converse | Observable programming | Open |

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- the state compression analogue (Article, Letter)
- [[concepts/free-entropy|Free Entropy]] -- governs all compression/programming rates
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- leading-order scaling
- [[definitions/regularized-free-entropy|Regularized Free Entropy]] -- the $O(1)$ state-dependent correction
- [[concepts/kks-theorem|KKS Theorem]] -- the factor of 1/2 between free entropy and QMDL
- [[concepts/holevo-information|Holevo Information]] -- used in converse proofs

## References

- buvzek1999optimal: Buzek, Derka, Massar -- optimal quantum clocks / sine state
- yang2020optimal: Yang, Renner, Chiribella -- optimal universal programming of unitary gates
- nielsen1997programmable: Nielsen and Chuang -- programmable quantum gate arrays
