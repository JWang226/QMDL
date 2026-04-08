# Holevo Information

**Appears in:** [[Article]] (Sec. 5, converse), [[Notes]] (Sec. 6, Sec. 8.5)

## Definition

For an ensemble $\{p_x, \rho_x\}$ of quantum states, the **Holevo information** (or Holevo $\chi$-quantity) is:

$$\chi_H = S\left(\sum_x p_x \rho_x\right) - \sum_x p_x S(\rho_x)$$

where $S(\rho) = -\mathrm{Tr}[\rho\log\rho]$ is the von Neumann entropy. It equals the mutual information $I(X:Q)$ between the classical label $X$ and the quantum system $Q$ carrying the state $\rho_x$.

## Intuition

The Holevo bound is the fundamental limit on classical information extraction from quantum states: no measurement on $\rho_x$ can yield more than $\chi_H$ bits of information about the label $x$. Equivalently, if you encode classical data into quantum states and then try to read it back, the Holevo quantity caps how much you can recover.

For converse proofs in quantum compression, the logic runs backwards: if a compressed quantum memory has dimension $|M|$, then the compressed state can carry at most $\log|M|$ bits of Holevo information about whatever parameter was used to prepare it. This translates a dimension bound on the memory into an information-theoretic inequality.

## Role in the State Compression Converse (Article, Sec. 5)

The converse for QMDL needs to show that the memory $|M_n|$ must be at least $\log \dim \mathcal{H}_\lambda$ for each Schur sector. The argument in the Article uses the [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]] as the primary tool for this (see Proposition 4). The Holevo bound provides a complementary perspective:

Consider the continuous Haar ensemble $\mathcal{E} = \{dg, (U(g)\rho U(g)^\dagger)^{\otimes n}\}$ and a compression code $(\mathcal{E}_{\mathrm{enc}}, \mathcal{D})$. By the data processing inequality:

$$\log|M| \geq \chi_H(\mathcal{E}_{\mathrm{enc}}(\mathcal{E})) \geq \chi_H(\mathcal{D} \circ \mathcal{E}_{\mathrm{enc}}(\mathcal{E})) \geq \chi_H(\mathcal{E}) - O(\varepsilon \log n)$$

The Holevo information of the Haar ensemble decomposes via Schur-Weyl duality. The ensemble mixture is $\mathrm{U}(d)$-invariant, so by Schur's lemma it is flat within each irrep block. Computing the Holevo information gives $\chi_H(\mathcal{E}) = \sum_\lambda p_\lambda \log \dim V_\lambda - f(\mathbf{p})$, where $f(\mathbf{p}) \sim O(1)$ is a remainder involving the entropies of the sector states. The compressed state of dimension $|M|$ can carry at most $\log|M|$ bits about the eigenbasis parameter $g \in \mathrm{U}(d)$, yielding the lower bound.

## Role in the Unitary Programming Converse (Notes, Sec. 8.5)

In the unitary programming problem (from the Notes), one seeks a program state $\sigma_U$ of dimension $D$ and a universal processor $\mathcal{P}$ such that $\|\mathcal{P}(\cdot \otimes \sigma_U) - U(\cdot)U^\dagger\|_\diamond \leq \varepsilon$ for all $U$ in an $f$-parameter unitary family.

The converse argument again uses the Holevo bound. The program state $\sigma_U$ lives in a $D$-dimensional space, so any measurement on it can extract at most $\log D$ bits about the parameter $x$ labeling $U_x$. The key steps are:

1. By the data processing inequality, $\log|M| \geq I_H(\mathcal{U}_x^{\otimes m}(\Phi_m), dp_x) - O(m\sqrt{\varepsilon}\log d_m)$, where $\Phi_m$ is a suitable input state and $d_m$ is the effective dimension.

2. Choosing $\Phi_m$ to be the optimal metrology state (the "sine-shaped state") and $dp_x$ to be uniform on a mesh of spacing $\sim 1/m$, the Holevo information is at least $f \log m - O(1)$, because the optimal estimator achieves Heisenberg-limited precision $\sim 1/m$.

3. Optimizing over $m \sim \delta/\sqrt{\varepsilon}$ gives the converse bound:

$$\log|M| \geq \frac{f}{2}\log(1/\varepsilon) - O(1)$$

This shows that the program dimension $D$ must grow as $\varepsilon^{-f/2}$, matching the achievability and confirming that [[concepts/physical-free-entropy|Physical Free Entropy]] governs the programming cost.

## Key Distinction: Holevo vs. Free Entropy $\chi$

The symbol $\chi$ is used for both the Holevo information $\chi_H$ and Voiculescu's [[concepts/free-entropy|Free Entropy]] $\chi$. These are completely different quantities: the Holevo $\chi_H$ is a von Neumann entropy difference measuring classical information in quantum states, while the free entropy $\chi$ is a logarithmic potential measuring the volume of matricial microstates. In this wiki, we use $\chi_H$ for Holevo information and $\chi$ (unsubscripted) for free entropy to avoid confusion.

## Related

- [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]] -- the algebraic approach to the same converse
- [[results/converse|Converse (State Compression)]] -- the full converse proof
- [[concepts/unitary-programming|Unitary Programming]] -- where the Holevo bound governs program dimension
- [[concepts/free-entropy|Free Entropy]] -- a different $\chi$ that should not be confused with Holevo $\chi_H$

## External References

- [Holevo's theorem (Wikipedia)](https://en.wikipedia.org/wiki/Holevo%27s_theorem)
- A. S. Holevo, "Bounds for the quantity of information transmitted by a quantum communication channel," *Problems of Information Transmission* 9(3), 177--183 (1973)
- M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge University Press (2000)
- [Accessible information (Wikipedia)](https://en.wikipedia.org/wiki/Accessible_information)
