# Unitary Programming Converse

**Source:** Notes Sec. 8.5 (line ~1613)

## Statement

For an $f$-parameter unitary family $\mathbb{F}$ parameterized by $\mathbb{T}^f$, any programming protocol achieving error $\varepsilon$ in diamond norm requires a program of dimension $D$ satisfying:

$$\log D \geq \left(\frac{f}{2} - \delta\right)\log(1/\varepsilon) - O(1)$$

for any $\varepsilon$-independent $\delta > 0$.

## Intuition

A quantum program state $\sigma_U$ of dimension $D$ can carry at most $\log D$ bits of [[concepts/holevo-information|Holevo Information]] about a classical parameter. But if the program successfully implements $U_x$ to error $\varepsilon$, then it implicitly encodes $x$ with precision $\sim \sqrt{\varepsilon}$ per parameter. Encoding $f$ continuous parameters to this precision requires at least $(f/2)\log(1/\varepsilon)$ bits of information. Balancing these two bounds yields the converse.

## Proof Sketch

**Main idea:** A program of dimension $D$ carries at most $\log D$ bits of Holevo information. But $m$ uses of the programmed channel applied to an optimal metrology state encode $f \log m$ bits about the parameter $x$. Choosing $m \sim 1/\sqrt{\varepsilon}$ balances the channel uses against the error penalty ($4m\sqrt{2\varepsilon}$ corruption term), giving $\log D \geq (f/2)\log(1/\varepsilon) - O(1)$.

---

### Extended Proof

The argument proceeds in three steps, following the strategy of Yang et al. (2020).

**Step 1: Holevo bound on program information.** Suppose $(\sigma_U, \mathcal{P})$ is an $\varepsilon$-programming scheme: $\|\mathcal{P}(\cdot \otimes \sigma_{U_x}) - U_x(\cdot)U_x^\dagger\|_\diamond \leq \varepsilon$. The program state $\sigma_{U_x}$ lives in a $D$-dimensional Hilbert space.

Consider applying $\mathcal{U}_x^{\otimes m}$ (the programmed channel, $m$ times) to a suitable input state $\Phi_m$. By the Holevo bound, the mutual information between the parameter $x$ (drawn from a prior $dp_x$) and the output quantum state is bounded:

$$I_H\bigl(\mathcal{U}_x^{\otimes m}(\Phi_m),\, dp_x\bigr) \leq \log D + 4m\sqrt{2\varepsilon}\log d_m + 1$$

where $d_m \leq (m + d^2 - 1)^{d^2 - 1}$ bounds the dimension of the output ensemble's support.

**Step 2: Lower-bound the Holevo information using optimal metrology.** Choose $\Phi_m$ to be the YRC sine-shaped state (the optimal state for quantum metrology with $m$ uses of $U_x$), and $dp_x$ to be uniform on a mesh $\mathbb{M}^f \subset \mathbb{T}^f$ with spacing $C/m$, so that $|\mathbb{M}^f| \geq (Lm/C)^f$ and $\log|\mathbb{M}^f| = f\log m + O(1)$.

The sine-shaped state achieves Heisenberg-limited estimation: applying the optimal covariant measurement yields an estimate $\hat{X}$ with:

$$P(|\hat{X} - X| > c/m) \leq P_e(m)$$

where $P_e(m) \to 0$ faster than logarithmically. Rounding $\hat{X}$ to the nearest mesh point $X'$ gives an effective classical channel $X \to X'$ with error probability at most $P_e(m)$. By data processing and Fano's inequality:

$$I_H\bigl(\mathcal{U}_x^{\otimes m}(\Phi_m),\, dp_x\bigr) \geq I(X : X') \geq f\log m - o(1)$$

**Step 3: Optimize the number of uses $m$.** Combining Steps 1 and 2:

$$\log D \geq f\log m - 4m\sqrt{2\varepsilon}\cdot(d^2 - 1)\log m - O(1)$$

$$= \bigl(f - 4m\sqrt{2\varepsilon}/(d^2 - 1)\bigr)\log m - O(1)$$

Now choose $m \sim \delta / \sqrt{\varepsilon}$ for any fixed $\delta > 0$. Then $4m\sqrt{2\varepsilon}/(d^2 - 1) \to 0$ as a controllable correction, and $\log m = \frac{1}{2}\log(1/\varepsilon) + O(1)$. Substituting:

$$\log D \geq (f - \delta')\cdot \frac{1}{2}\log(1/\varepsilon) - O(1) = \left(\frac{f}{2} - \delta\right)\log(1/\varepsilon) - O(1)$$

for arbitrarily small $\delta > 0$.

## Open: Tight $O(1)$ Constant

The converse gives $(f/2)\log(1/\varepsilon) - O(1)$, matching the achievability at leading order. The subleading $O(1)$ term is not tight -- see [[open-questions/unitary-subleading|Open: Subleading Term for Unitary Programming]]. The authors ask whether the Kirillov character formula could help pin down this constant.

## Dependencies

- [[concepts/holevo-information|Holevo Information]] -- the fundamental bound on classical information extractable from quantum states
- Fano's inequality -- converting error probability into mutual information bounds
- Data processing inequality -- $I(X:Q) \geq I(X:X')$ for any post-processing $Q \to X'$
- Heisenberg-limited metrology with YRC sine-shaped states (Yang et al. 2020)

## Used By

- [[concepts/unitary-programming|Unitary Programming]] -- this is the converse half
- [[results/spectral-measurement-converse|Spectral Measurement Programming (Converse)]] -- reduces to this via the flag manifold

## External References

- [Yang, Chiribella, and Hayashi, "Optimal universal programming of unitary gates" (2020)](https://arxiv.org/abs/2001.05299)
- [Holevo's theorem (Wikipedia)](https://en.wikipedia.org/wiki/Holevo%27s_theorem)
