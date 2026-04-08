# Observable Expectation Programming (Achievability)

**Source:** Notes Sec. 9.3.1 (line ~1806)

## Statement

For programming the expectation value $\mathrm{Tr}[H\rho]$ of a Hermitian observable $H$ on $\mathbb{C}^d$ to precision $\varepsilon$, a program of dimension $D$ suffices with:

$$\log D \leq \frac{d^2 \cdot \delta(H)}{2}\log(1/\varepsilon) + O(1)$$

Here the task is: given a program $\sigma_H$ and sufficiently many copies $\rho^{\otimes n}$ of an arbitrary state $\rho$, a universal processor $\mathcal{P}$ outputs a value $\varepsilon$-close to $\mathrm{Tr}[H\rho]$. The number of copies $n$ is unconstrained; the program size is the resource being optimized.

## Intuition

Expectation estimation is a *weaker* task than spectral measurement programming: knowing the full POVM $\{P_a\}$ lets you compute $\mathrm{Tr}[H\rho] = \sum_a E_a \mathrm{Tr}[P_a \rho]$, but estimating $\mathrm{Tr}[H\rho]$ does not require knowing each $P_a$ individually. Thus the spectral measurement achievability automatically gives an upper bound. But there is also a more direct route via state compression that reveals the connection to [[concepts/free-entropy|Free Entropy]] more clearly.

## Proof Sketch

**Main idea:** Two approaches give the same bound. (1) Spectral measurement programming is a harder task, so its achievability carries over. (2) More directly: normalize $H$ to a density matrix $\tilde{H}$, compress $\tilde{H}^{\otimes n}$ using the QMDL protocol as the program, then use the swap test with the unknown state $\rho$ to estimate $\mathrm{Tr}[H\rho]$. Both give program cost $(d^2 \delta(H)/2)\log(1/\varepsilon) + O(1)$.

---

### Extended Proof

### Approach 1: Via spectral measurement (trivial reduction)

Since spectral measurement programming is a strictly harder task (it recovers the full Born-rule statistics, not just one expectation value), the achievability bound from [[results/spectral-measurement-achievability|Spectral Measurement Programming (Achievability)]] carries over directly:

$$\log D \leq \frac{d^2 \cdot \delta(H)}{2}\log(1/\varepsilon) + O(1)$$

### Approach 2: Via state compression (direct construction)

This approach converts $H$ into a density matrix and uses [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] (state compression) as the programming primitive.

**Step 1: Turn $H$ into a density matrix.** Shift $H$ to make it positive: $H' = H - E_0 I$ where $E_0$ is the minimal eigenvalue. Normalize to a density matrix:

$$\tilde{H} = \frac{H'}{\mathrm{Tr}[H']} = \frac{H - E_0 I}{\mathrm{Tr}[H] - E_0 d}$$

The observable $\tilde{H}$ has the same eigenbasis as $H$, and its eigenvalues are a positive rescaling of those of $H$.

**Step 2: Compress copies of $\tilde{H}$.** Set $n = \varepsilon^{-2}$ (the number of copies needed for statistical precision). The program $\sigma_H$ is the optimal compression of $\tilde{H}^{\otimes n}$, which by the [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] result has size:

$$|\sigma_H| = \frac{d^2}{2}\chi_{\mathrm{phy}}(\tilde{H}; 1/n)$$

A calculation shows:

$$|\sigma_H| = d^2 \chi_{\mathrm{phy}}(H; \varepsilon) - \log(\mathrm{Tr}[H] - E_0 d)$$

so the program size is controlled by the physical free entropy of $H$ up to an $H$-dependent constant.

**Step 3: Simulate the expectation.** To estimate $\mathrm{Tr}[H\rho]$, the processor:
1. Decompresses $\sigma_H$ to recover (approximately) $\tilde{H}^{\otimes n}$.
2. Performs the swap test between $\tilde{H}$ and $\rho$ for $n$ rounds, estimating $\mathrm{Tr}[\rho \tilde{H}]$.
3. Rescales: $\mathrm{Tr}[H\rho] = (\mathrm{Tr}[H] - E_0 d) \cdot \mathrm{Tr}[\rho \tilde{H}] + E_0$.

**Step 4: Error analysis.** Two sources of error:
- *Decompression error*: the decoded state $\mathcal{D}(\sigma_H)$ approximates $\tilde{H}^{\otimes n}$ with error $\sim n^{-1/2} \sim \varepsilon$. This causes a systematic bias of $O(\varepsilon)$.
- *Statistical error*: the swap test with $n = \varepsilon^{-2}$ rounds has standard deviation $O(n^{-1/2}) = O(\varepsilon)$.

The total error is $O(\varepsilon)$ as required.

**Remark on the error parameter.** The spectral measurement programming uses error $\varepsilon$ in the diamond-norm sense, while the expectation programming uses $\varepsilon$ as an additive error on $\mathrm{Tr}[H\rho]$. The factor-of-2 difference in the $\log(1/\varepsilon)$ coefficient between these formulations is consistent: estimating the full measurement statistics from the spectral POVM to precision $\varepsilon$ requires $n \sim \varepsilon^{-2}$ repetitions (Chernoff bound), recovering the same scaling.

## Open: Converse

The converse for observable expectation programming is **open**. It is unclear whether the spectral measurement approach is optimal for the expectation task, or whether the weaker requirement allows for smaller programs. See [[open-questions/observable-expectation-converse|Observable Expectation Converse]].

## Dependencies

- [[results/spectral-measurement-achievability|Spectral Measurement Programming (Achievability)]] -- gives the bound via Approach 1
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- the state compression result used in Approach 2
- [[concepts/free-entropy|Free Entropy]] -- $\chi_{\mathrm{phy}}(H; \varepsilon)$ controls the program size
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- $\delta(H) = 1 - \sum_a g_a^2/d^2$ determines the leading order
- Swap test -- used for estimating $\mathrm{Tr}[\rho \tilde{H}]$ from copies

## Used By

- [[concepts/observable-programming|Observable Programming]] -- this is one of two formulations of observable programming

## External References

- [Swap test (Wikipedia)](https://en.wikipedia.org/wiki/Swap_test)
