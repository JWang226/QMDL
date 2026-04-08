# Estimation-Programming Lemma

**Label:** `lem:estprog` (Notes)
**Source:** Notes line ~1528

## Statement

Consider any estimation protocol for a parameter $x \in \mathbb{T}^f$ with MSE $\varepsilon \ll 1$ and conditional probability density $p(\hat{x}|x)$ satisfying:

1. **Shift-invariance**: there exists a density $q$ such that $p(\hat{x}|x) = q(\hat{x} - x)$ for all $\hat{x}, x$.
2. **Concentrated tail**: there exists $\alpha > 0$ such that $1 - \int_{T_\varepsilon} dy\, q(y) = o(\varepsilon)$, where $T_\varepsilon := \{y : |y_j| \leq \varepsilon^\alpha, \forall j\}$.
3. **Local symmetry**: $q(y) = q(-y)$ for all $y \in T_\varepsilon$.

Then the estimation-based programming protocol $\int d\hat{x}\, p(\hat{x}|x)\, \mathcal{U}_{\hat{x}}$ has error:

$$\varepsilon_{\mathrm{prog}} \leq \varepsilon \cdot \frac{1}{2}\left\|\frac{\partial^2 \mathcal{U}_x}{\partial x_j^2}\right\|_\diamond + o(\varepsilon)$$

where $\|\cdot\|_\diamond$ is the diamond norm. We further assume the $k$-th order derivatives are bounded as $\|\partial^k \mathcal{U}_x / \partial x_{j_1} \cdots \partial x_{j_k}\|_\diamond \leq (2h)^k$ for a universal constant $h > 0$.

## Intuition

The estimation-then-program paradigm works as follows: given copies of the parameter (or a program state encoding $x$), first estimate $\hat{x}$, then prepare and execute $U_{\hat{x}}$. The error comes from implementing $U_{\hat{x}}$ instead of the true $U_x$. The key insight is that the first-order error vanishes by symmetry, so the dominant contribution is second-order -- proportional to the MSE times the "curvature" of the unitary family.

## Proof Sketch

**Main idea:** Taylor-expand the unitary channel $\mathcal{U}_{x+y}$ around $x$ in diamond norm. The shift-invariance of the estimator lets us change variables to $y = \hat{x} - x$; local symmetry $q(y) = q(-y)$ kills all odd-order terms; the concentrated-tail condition restricts the integral to a small box where the expansion converges. The dominant contribution is the second-order (MSE) term; higher-order terms are $o(\varepsilon)$.

---

### Extended Proof

**Step 1: Reduce to a local integral.** The programming error is:

$$\varepsilon_{\mathrm{prog}} = \sup_x \frac{1}{2}\left\|\int d\hat{x}\, p(\hat{x}|x)\, \mathcal{U}_{\hat{x}} - \mathcal{U}_x\right\|_\diamond$$

By shift-invariance (condition 1), substitute $y = \hat{x} - x$ so that $p(\hat{x}|x) = q(y)$. By the concentrated tail condition (condition 2), the integral outside the small box $T_\varepsilon$ contributes only $o(\varepsilon)$, so:

$$\varepsilon_{\mathrm{prog}} \leq \sup_x \frac{1}{2}\left\|\int_{T_\varepsilon} dy\, q(y)\, (\mathcal{U}_{x+y} - \mathcal{U}_x)\right\|_\diamond + o(\varepsilon)$$

**Step 2: Taylor expand $\mathcal{U}_{x+y}$ around $x$.** Since $T_\varepsilon$ is a small neighborhood, expand:

$$\mathcal{U}_{x+y} = \mathcal{U}_x + \sum_{j=1}^f y_j \frac{\partial \mathcal{U}_x}{\partial x_j} + \frac{1}{2}\sum_{j_1, j_2} y_{j_1} y_{j_2} \frac{\partial^2 \mathcal{U}_x}{\partial x_{j_1} \partial x_{j_2}} + \cdots$$

Substituting into the integral and using the triangle inequality for the diamond norm:

$$\varepsilon_{\mathrm{prog}} \leq \sum_{k=1}^\infty \sum_{j_1,\ldots,j_k} \left|\int_{T_\varepsilon} dy\, q(y)\, y_{j_1} \cdots y_{j_k}\right| \cdot \frac{1}{2}\left\|\frac{\partial^k \mathcal{U}_x}{\partial x_{j_1} \cdots \partial x_{j_k}}\right\|_\diamond + o(\varepsilon)$$

**Step 3: Odd moments vanish by symmetry.** Since $T_\varepsilon$ is symmetric and $q(y) = q(-y)$ on $T_\varepsilon$ (condition 3), all odd-order moments vanish:

$$\int_{T_\varepsilon} dy\, q(y)\, y_j = 0$$

More generally, $\int q(y)\, y_{j_1} \cdots y_{j_k}\, dy = 0$ whenever $k$ is odd or any index appears an odd number of times. In particular, the entire $k = 1$ (linear) and $k = 3$ (cubic) terms vanish.

**Step 4: Bound higher even moments.** For even $k$, the $k$-th moment is bounded by:

$$\left|\int_{T_\varepsilon} dy\, q(y)\, y_{j_1} \cdots y_{j_k}\right| \leq \varepsilon^{1 + (k-2)\alpha}$$

The $k = 2$ diagonal terms give $\int q(y)\, y_j^2\, dy \leq \varepsilon$ (the MSE), while for $k \geq 4$ the extra factor $\varepsilon^{(k-2)\alpha}$ makes these terms subleading.

**Step 5: Collect.** The dominant contribution comes from $k = 2$. Combined with the derivative bound $\|\partial^k \mathcal{U}_x\|_\diamond \leq (2h)^k$, the $k \geq 4$ terms sum to $O(\varepsilon^{1+2\alpha}) = o(\varepsilon)$:

$$\varepsilon_{\mathrm{prog}} \leq \varepsilon \cdot \sum_{j=1}^f \frac{1}{2}\left\|\frac{\partial^2 \mathcal{U}_x}{\partial x_j^2}\right\|_\diamond + o(\varepsilon)$$

**Why the three conditions matter:**
- *Shift-invariance* lets us change variables to $y = \hat{x} - x$, making the error distribution independent of the true parameter.
- *Local symmetry* kills the first-order term, ensuring the MSE (not the bias) is the right measure of estimation quality.
- *Concentrated tail* ensures we can restrict attention to a small neighborhood where the Taylor expansion converges.

## Role in the Project

This lemma is the bridge between estimation theory and programming theory for [[concepts/unitary-programming|Unitary Programming]]. It says that any good estimator can be converted into a good programmer, with the programming error controlled by the MSE times the curvature of the unitary family. Combined with the [[concepts/sine-state|Sine State]] (which achieves Heisenberg-limited MSE $\sim \pi^2 f / D^2$), it yields the [[results/sine-state-programming|Sine-State Programming Proposition]].

## Dependencies

- Taylor expansion of the unitary channel $\mathcal{U}_x$ in diamond norm
- Derivative bound: $\|\partial^k \mathcal{U}_x / \partial x_{j_1} \cdots \partial x_{j_k}\|_\diamond \leq (2h)^k$ (satisfied, e.g., when $U_x = e^{-iH \cdot x}$ with $h = \max_j \|H_j\|$)
- Triangle inequality and absolute homogeneity of the diamond norm

## Used By

- [[results/sine-state-programming|Sine-State Programming Proposition]] -- plugging in the sine state MSE
- [[concepts/unitary-programming|Unitary Programming]] -- the achievability half
- [[results/spectral-measurement-achievability|Spectral Measurement Programming (Achievability)]] -- via the sine-state chain

## External References

- [Quantum metrology (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_metrology)
- [Giovannetti, Lloyd, and Maccone, "Quantum-enhanced measurements: beating the standard quantum limit" (2004)](https://arxiv.org/abs/quant-ph/0412078)
