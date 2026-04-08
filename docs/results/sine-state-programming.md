# Sine-State Programming Proposition

**Source:** Notes line ~1589

## Statement

The programming protocol based on sine-state estimation (cf. Notes Sec. 8.3) for an $f$-parameter unitary family $\{U_x\}_{x \in \mathbb{T}^f}$ with program dimension $D$ per parameter achieves error:

$$\varepsilon_{\mathrm{prog}} \leq \frac{1}{D^2} \cdot \frac{f\pi^2}{2}\left\|\frac{\partial^2 \mathcal{U}_x}{\partial x_j^2}\right\|_\diamond + o\left(\frac{1}{D^2}\right)$$

## Intuition

The sine state is the optimal quantum state for single-parameter phase estimation at the Heisenberg limit. By using $f$ independent sine states (one per parameter), we estimate all $f$ components of $x$ with total MSE scaling as $1/D^2$. The [[results/estimation-programming-lemma|Estimation-Programming Lemma]] then converts this estimation quality directly into a programming error bound.

## Proof Sketch

**Main idea:** Use $f$ independent sine states (one per parameter of the unitary family), each of dimension $D$, achieving Heisenberg-limited MSE $\sim f\pi^2/D^2$. Verify the three conditions of the Estimation-Programming Lemma (shift-invariance, local symmetry, concentrated tail), then substitute to get programming error $\leq f\pi^2 C / (2D^2)$. Inverting for target error $\varepsilon$ gives program cost $f \log D = (f/2)\log(1/\varepsilon) + O(1)$.

---

### Extended Proof

**Step 1: The sine state and its MSE.** For each parameter $x_j$, the program uses a sine-shaped state of dimension $D$:

$$|\sin_{x_j}\rangle = \sqrt{\frac{2}{D}} \sum_{m=0}^{D-1} \sin\frac{(m + 1/2)\pi}{D}\, e^{imx_j} |m\rangle$$

The full program state is the product $|P_x\rangle = |\sin_{x_1}\rangle \otimes \cdots \otimes |\sin_{x_f}\rangle$. To execute the programmed unitary, one measures each $|\sin_{x_j}\rangle$ in the $D$-dimensional Fourier basis and operates $U_{\hat{x}}$ according to the estimate $\hat{x}$.

The sine state achieves the Heisenberg limit for phase estimation. The MSE of the resulting estimator is:

$$\varepsilon_{\mathrm{est}} = \frac{f\pi^2}{D^2} + o(D^{-2})$$

which scales as $\pi^2/(D+1)^2 \approx \pi^2/D^2$ per parameter.

**Step 2: Verify the conditions of the Estimation-Programming Lemma.** The conditional probability density is:

$$p(\hat{x}|x) = \prod_{j=1}^f \left|\langle\phi_{\hat{x}_j}|\sin_{x_j}\rangle\right|^2$$

This factored form immediately gives:
- *Condition 1 (shift-invariance)*: $p(\hat{x}|x) = q(\hat{x} - x)$, since the overlap depends only on the difference.
- *Condition 3 (local symmetry)*: $q(y) = q(-y)$ for small $y$, by the symmetric structure of the sine state.
- *Condition 2 (concentrated tail)*: The density has width $\sim 1/D$, so for any $\alpha < 1/2$, the tail outside $T_\varepsilon$ is $o(\varepsilon_{\mathrm{est}})$.

**Step 3: Substitute into the estimation-programming lemma.** Applying the [[results/estimation-programming-lemma|Estimation-Programming Lemma]] with $\varepsilon = f\pi^2/D^2$:

$$\varepsilon_{\mathrm{prog}} \leq \frac{f\pi^2}{D^2} \cdot \frac{1}{2}\left\|\frac{\partial^2 \mathcal{U}_x}{\partial x_j^2}\right\|_\diamond + o(1/D^2)$$

Writing $C = \|\partial^2 \mathcal{U}_x / \partial x_j^2\|_\diamond$ for the curvature constant (which depends on the unitary family but not on $D$), this is:

$$\varepsilon_{\mathrm{prog}} \leq \frac{f\pi^2 C}{2D^2} + o(1/D^2)$$

**Step 4: Invert for target error.** For a target programming error $\varepsilon$, set $\varepsilon_{\mathrm{prog}} = \varepsilon$ and solve for $D$:

$$D \sim \sqrt{\frac{f\pi^2 C}{2\varepsilon}}$$

Taking logarithms:

$$\log D = \frac{1}{2}\log\frac{1}{\varepsilon} + \frac{1}{2}\log\frac{f\pi^2 C}{2} = \frac{1}{2}\log\frac{1}{\varepsilon} + O(1)$$

The total program cost is $f \log D$ (since we use $f$ independent sine states each of dimension $D$):

$$f \log D = \frac{f}{2}\log\frac{1}{\varepsilon} + O(1)$$

This matches the physical [[concepts/free-entropy|Free Entropy]] of the unitary at leading order: the free entropy dimension $\delta(U) = 1 - \sum_i g_i^2/d^2$ determines the number of real parameters $f = d^2 \delta(U)$, and the leading-order program size is $(f/2)\log(1/\varepsilon)$.

## Dependencies

- [[results/estimation-programming-lemma|Estimation-Programming Lemma]] -- the general estimation-to-programming reduction
- [[concepts/sine-state|Sine State]] -- achieves Heisenberg-limited MSE $\pi^2/D^2$ per parameter
- Heisenberg limit for quantum phase estimation

## Used By

- [[concepts/unitary-programming|Unitary Programming]] -- this is the achievability half
- [[results/spectral-measurement-achievability|Spectral Measurement Programming (Achievability)]] -- reduces to this via the flag manifold

## External References

- [Quantum phase estimation algorithm (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_phase_estimation_algorithm)
- [Buzek, Derka, and Massar, "Optimal quantum clocks" (1999)](https://arxiv.org/abs/quant-ph/9808042)
