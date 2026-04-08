# Sine State

**Appears in:** Notes (Sec. 8.2-8.3)

## Definition

For a $D$-dimensional program register estimating a parameter $y \in [0, 2\pi)$, the **sine state** is:

$$|\mathrm{sin}_y\rangle = \sqrt{\frac{2}{D+1}} \sum_{k=1}^{D} \sin\left(\frac{k\pi}{D+1}\right) e^{iky} |k\rangle$$

## Why the Sine State?

The sine state is not just *a* good state for phase estimation -- it is essentially the *best*. Its amplitudes $\sin(k\pi/(D+1))$ match the optimal Bayesian prior for estimating an unknown phase uniformly distributed on $[0, 2\pi)$. More precisely, if one computes the state that minimizes the mean squared error of phase estimation averaged over a flat prior, the answer is exactly the sine state.

**Intuition:** Think of the amplitudes $\sin(k\pi/(D+1))$ as a discrete half-sine wave. This shape is optimal because it concentrates the Fourier transform of the state as tightly as possible around the target phase $y$ while respecting the boundary conditions of the finite-dimensional Hilbert space. States with flat amplitudes (like the uniform superposition) waste resources on sidelobes; states that are too sharply peaked in the number basis sacrifice bandwidth.

## Connection to Optimal Quantum Clocks (Buzek-Derka-Massar)

The sine state was introduced by Buzek, Derka, and Massar (1999) in the context of **optimal quantum clocks**. Their question was: given a reference frame for time encoded in $D$ energy levels, what is the most precise clock you can build? The answer is a clock whose state is precisely $|\mathrm{sin}_y\rangle$. The connection to our project is that unitary programming requires estimating the parameter $x$ of $U_x$, which is mathematically identical to estimating the "time" of a quantum clock with $D$ levels.

The sine state achieves the **Heisenberg limit**: the mean squared error scales as $1/D^2$ (rather than the standard quantum limit $1/D$), which is the best possible scaling for $D$-dimensional phase estimation.

## Properties

1. **Optimal phase estimation**: Achieves mean squared error $\mathrm{MSE} \sim \pi^2/(D+1)^2$, which is the Heisenberg limit
2. **Non-negative amplitudes**: The $\sin(k\pi/(D+1))$ coefficients are all positive, which simplifies analysis and ensures the state has no phase cancellations
3. **Concentrated Fourier transform**: The state's position-space representation is sharply peaked around $y$, with sidelobe suppression comparable to a Dirichlet kernel

## Role in the Project

The sine state is the key ingredient in the [[concepts/unitary-programming|Unitary Programming]] achievability proof:

1. Estimate the unitary parameter $x$ using $D$ copies
2. Prepare $|\mathrm{sin}_{\hat{x}}\rangle$ encoding the estimate
3. The processor uses this to approximately implement $U_x$

The resulting programming error is $\varepsilon \sim f\pi^2/(2D^2) \cdot \|d^2U_x/dx^2\|_\diamond$, giving the rate $\log D = \frac{f}{2}\log(1/\varepsilon) + O(1)$.

## References

- buvzek1999optimal: Optimal quantum clocks (Buzek-Derka-Massar 1999) -- introduced the sine state for phase estimation

## Related

- [[concepts/unitary-programming|Unitary Programming]]
- [[results/estimation-programming-lemma|Estimation-Programming Lemma]]

## External References

- [Quantum phase estimation (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_phase_estimation_algorithm)
- V. Buzek, R. Derka, and S. Massar, "Optimal quantum clocks," *Phys. Rev. Lett.* 82, 2207--2210 (1999)
- [Heisenberg limit (Wikipedia)](https://en.wikipedia.org/wiki/Heisenberg_limit)
- [Quantum metrology (Wikipedia)](https://en.wikipedia.org/wiki/Quantum_metrology)
