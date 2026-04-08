# Spectral Measurement Programming (Converse)

**Source:** Notes Sec. 9.2.2 (line ~1741)

## Statement

For a Hermitian observable $H = \sum_{a=1}^k E_a P_a$ on $\mathbb{C}^d$ with eigenspace multiplicities $g_1, \ldots, g_k$, any programming protocol for the spectral measurement $\{P_a\}$ achieving error $\varepsilon$ requires a program of dimension $D$ satisfying:

$$\log D \geq \frac{d^2 \cdot \delta(H)}{2}\log(1/\varepsilon) - O(1)$$

matching the [[results/spectral-measurement-achievability|Spectral Measurement Programming (Achievability)]] at leading order.

## Intuition

The key idea is that measurement programming *implies* unitary estimation: if you can program the spectral measurement, you can extract information about the eigenbasis from a known input state. This reverses the achievability argument (which turned unitary programming into measurement programming) and lets us invoke the [[results/unitary-programming-converse|Unitary Programming Converse]] on the flag manifold.

## Proof Sketch

**Main idea:** Reverse the achievability reduction: any measurement programming scheme $(\sigma_H, \{\Pi_a\})$ implicitly implements the eigenbasis-rotation unitary on the flag manifold (feeding known eigenstates $P_j$ as inputs recovers $U_P^\dagger P_j U_P$). Apply the unitary programming converse on the $f = d^2 \delta(H)$-dimensional flag manifold to get $\log D \geq (f/2)\log(1/\varepsilon) - O(1)$.

---

### Extended Proof

The argument reverses the reduction used in the achievability proof to turn any measurement programming scheme into a unitary programming scheme, then applies the unitary converse.

**Step 1: From measurement programming to a CPTP channel.** Suppose we have a measurement programming scheme $(\sigma_H, \{\Pi_a\})$ such that:

$$\mathrm{Tr}\, \rho \otimes \sigma_H \cdot \Pi_a \approx \mathrm{Tr}\, P_a \rho, \quad \forall\, \rho$$

Construct a CP unital map $\mathcal{P}^\dagger(\cdot) = \sum_j \Pi_j \langle j|\cdot|j\rangle$ so that $\mathcal{P}^\dagger(|i\rangle\langle i|) = \Pi_i$. Its dual $\mathcal{P}$ is a CPTP map satisfying:

$$\mathrm{Tr}\, \mathcal{P}(\rho \otimes \sigma_H) \cdot |i\rangle\langle i| \approx \mathrm{Tr}\, P_i \rho$$

**Step 2: Extract the eigenbasis unitary.** Each projector set $\{P_a\}$ corresponds to a unique unitary (modulo the stabilizer) $U_P$ in the [[concepts/flag-manifold|Flag Manifold]]:

$$P_a = U_P^\dagger \left(\sum_{i \in I_a} |i\rangle\langle i|\right) U_P$$

The measurement programming condition then reads:

$$\mathrm{Tr}\, U_P^\dagger \rho\, U_P \cdot |i\rangle\langle i| \approx \mathrm{Tr}\, \mathcal{P}(\rho \otimes \sigma_H) \cdot |i\rangle\langle i|$$

**Step 3: Recover the unitary action from known inputs.** Setting $\rho = P_j$ (which is a known state once we know the eigenbasis):

$$\mathrm{Tr}\, \mathcal{P}(P_j \otimes \sigma_H) \cdot |i\rangle\langle i| \approx \delta_{ij}$$

This implies $\mathcal{P}(P_j \otimes \sigma_H) \approx |j\rangle\langle j| = U_P^\dagger P_j U_P$. In other words, $(\sigma_H, \mathcal{P})$ effectively implements the unitary channel $\rho \mapsto U_P^\dagger \rho\, U_P$ when the input happens to be an eigenstate of $H$.

More generally, $(\sigma_H, \mathcal{P})$ constitutes a universal programming scheme for unitaries on the flag manifold:

$$U(d) \big/ \bigl(U(g_1) \times \cdots \times U(g_k)\bigr)$$

**Step 4: Apply the unitary programming converse.** The flag manifold has real dimension $f = d^2 - \sum_a g_a^2 = d^2 \cdot \delta(H)$. By the [[results/unitary-programming-converse|Unitary Programming Converse]]:

$$\log D \geq \frac{f}{2}\log(1/\varepsilon) - O(1) = \frac{d^2 \cdot \delta(H)}{2}\log(1/\varepsilon) - O(1)$$

**The degenerate case.** The same argument works when $H$ has degenerate eigenvalues. Starting from $(\sigma_H, \{\Pi_a\})$ with $k < d$ projectors of general rank, one obtains $\mathcal{P}(P_a \otimes \sigma_H) \approx \sum_{i \in I_a} |i\rangle\langle i|$, which gives a programming scheme for the coset $U(d)/(U(g_1) \times \cdots \times U(g_k))$ with $f = d^2 - \sum_a g_a^2$. The converse bound then gives $\log D \geq (d^2\delta(H)/2)\log(1/\varepsilon) - O(1)$.

## Dependencies

- [[results/unitary-programming-converse|Unitary Programming Converse]] -- the information-theoretic lower bound that is invoked in Step 4
- [[concepts/flag-manifold|Flag Manifold]] -- the parameter space for the eigenbasis, with $f = d^2 - \sum g_a^2$ real degrees of freedom
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- $\delta(H) = 1 - \sum_a g_a^2/d^2$ determines the leading coefficient

## Used By

- [[concepts/observable-programming|Observable Programming]] -- combined with the achievability, this pins down the spectral measurement programming cost at leading order
- [[results/spectral-measurement-achievability|Spectral Measurement Programming (Achievability)]] -- matched at leading order, confirming optimality

## External References

- [Yang, Renner, and Chiribella, "Optimal universal programming of unitary gates" (2020)](https://doi.org/10.1103/PhysRevLett.125.210501)
