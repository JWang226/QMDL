# Quantum Minimum Description Length (QMDL)

**Appears in:** [[Letter]], [[Article]]

## Intuition

Given $n$ copies of a density matrix $\rho^{\otimes n}$, how small a quantum memory do you need to store a faithful description? This is NOT Schumacher compression (which preserves purifications). QMDL compression only needs to recover the **state itself**, not its correlations with a reference system.

Concretely: you know the spectrum of $\rho$ (its eigenvalues), but not its eigenbasis. You want to compress $\rho^{\otimes n}$ into a quantum system of dimension $|M_n|$ such that you can later decompress and recover $\rho^{\otimes n}$ with high fidelity.

The key insight is that since the spectrum is known, you only need to store the **eigenbasis** -- a point on a continuous manifold. The memory cost should therefore scale as $O(\log n)$ (not $O(n)$ like Schumacher), with the coefficient determined by the dimension of this manifold.

## The Compression Task

An $(|M|, \delta)$-code is a pair of quantum channels:
- **Encoder** $E: (\mathbb{C}^d)^{\otimes n} \to \mathbb{C}^{|M|}$ 
- **Decoder** $D: \mathbb{C}^{|M|} \to (\mathbb{C}^d)^{\otimes n}$

such that $\frac{1}{2}\|\rho^{\otimes n} - D \circ E(\rho^{\otimes n})\|_1 \leq \delta$.

The QMDL is the minimum $\log|M_n|$ such that $\delta_n \to 0$.

## Key Distinction from Schumacher Compression

| | Schumacher | QMDL |
|---|---|---|
| Preserves purification? | Yes | No |
| Rate (leading order) | $nS(\rho)$ | $O(\log n)$ |
| What's compressed | Quantum information | Classical description of eigenbasis |
| Entropy notion | von Neumann entropy | Free entropy |

The QMDL rate is only $O(\log n)$ because knowing the spectrum means you only need to describe the eigenbasis, which lives on a [[concepts/flag-manifold|Flag Manifold]] of dimension $r(2d-r-1)$ (when spectrum is non-degenerate with rank $r$).

## Main Result

For $\rho$ of rank $r$ with non-degenerate positive eigenvalues $x_1 > \cdots > x_r > 0$:

$$\log|M_n| = \frac{r(2d - r - 1)}{2}\log n + \sum_{i < j \leq r} \log(x_i - x_j) + (d-r)\sum_{i=1}^r \log x_i - \sum_{k=d-r}^{d-1} \log k! + o(1)$$

The first term ($\propto \log n$) is governed by [[concepts/free-entropy-dimension|Free Entropy Dimension]]. The second-order terms ($O(1)$) are governed by [[concepts/free-entropy|regularized free entropy]]. Together they equal $\frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1/2})$ plus universal constants.

## Proof Strategy: Achievability

The encoding protocol generalizes the Yang-Chiribella-Hayashi (YCH) scheme from qubits to qudits using the [[concepts/generalized-cloning-map|Generalized Cloning Map]].

### Encoding

1. **Schur transform.** Apply $V_{\mathrm{Schur}}$ to decompose $\rho^{\otimes n}$ into Schur-Weyl sectors:
$$\rho^{\otimes n} \simeq \bigoplus_\lambda q_\lambda (\rho_\lambda \otimes \tau_\lambda)$$

2. **Measure $\lambda$.** Perform a non-demolition measurement of the Young diagram label, obtaining some $\lambda$.

3. **Discard $M_\lambda$.** Throw away the multiplicity register $\tau_\lambda$ (it is maximally mixed and carries no information about the eigenbasis).

4. **Clone to target.** Apply the generalized cloning map $C_{\lambda \to \Lambda^*}$ to map $\rho_\lambda$ into a fixed target irrep $\Lambda^*$. Store the result in a quantum memory of dimension $d_{\Lambda^*}$.

### Target irrep construction

The target $\Lambda^*$ must dominate all typical $\lambda$ (so that $\Lambda^* - \lambda$ is a valid dominant weight for every typical sector). It is constructed as:

$$\Lambda^*_i = \lceil nx_i + (r - i)\xi_n \rceil, \quad \text{where } \xi_n = 2\sqrt{n\Delta_n/2} + 1$$

with $\Delta_n = (\log n)^2$. The padding $(r-i)\xi_n$ ensures the **dominance gap condition** $\Lambda^*_i - \Lambda^*_{i+1} \geq \lambda_i - \lambda_{i+1}$ holds for all typical $\lambda$: the macroscopic terms $n(x_i - x_{i+1})$ cancel between $\Lambda^*$ and $\lambda$, leaving $\xi_n - 1 \geq 2\epsilon_n$ where $\epsilon_n = \sqrt{n\Delta_n/2}$ is the maximum typical fluctuation. The choice $\xi_n = 2\epsilon_n + 1$ is the tightest buffer that absorbs both worst-case fluctuations and rounding errors.

### Decoding

1. **Sample $\lambda'$** from the empirical Schur-Weyl distribution $q_{\lambda'}$.
2. **Reverse clone:** apply $C_{\Lambda^* \to \lambda'}$.
3. **Reconstruct:** append a fresh maximally mixed multiplicity register $\tau_{\lambda'}$ and apply the inverse Schur transform.

### Error analysis

The total error splits into two terms:

$$\delta_n \leq \max_{\lambda \in \mathcal{T}} \frac{1}{2}\|C_{\Lambda^* \to \lambda} \circ C_{\lambda \to \Lambda^*}(\rho_\lambda) - \rho_\lambda\|_1 + \sum_{\lambda \notin \mathcal{T}} q_\lambda$$

**Typical sectors (first term).** For $\lambda$ in the typical set $\mathcal{T}_{p,n} = \{\lambda : \max_i |\lambda_i - nx_i| \leq \sqrt{n\Delta_n/2}\}$, the distance $d(\Lambda^*, \lambda) = O(\sqrt{n\Delta_n})$. By the [[results/cloning-fidelity|cloning fidelity theorem]], the round-trip fidelity is $1 - O(n^{-1/2+\varepsilon})$. The Fuchs-van de Graaf inequality converts this to trace distance $O(n^{-1/4+\varepsilon})$.

**Atypical tail (second term).** By Sanov's theorem (Lemma 5), $\sum_{\lambda \notin \mathcal{T}} q_\lambda \leq (n+1)^{r(r+1)/2} e^{-\Delta_n}$, which is superpolynomially small for $\Delta_n = (\log n)^2$.

**Memory cost.** Since the output lives in $H_{\Lambda^*}$, the memory cost is $\log d_{\Lambda^*}$. Since $\Lambda^*_i = nx_i + O(\sqrt{n\Delta_n})$, the [[concepts/weyl-dimension-formula|asymptotic Weyl dimension formula (Lemma 11)]] gives exactly the claimed rate, with the $O(\sqrt{n\Delta_n})$ padding vanishing into the $o(1)$ tail.

## Proof Strategy: Converse

The converse proves that no compression scheme can do better.

### Step 1: Haar-average and Markov inequality

Start with a code achieving worst-case error $\delta_n \to 0$ over all $g \in U(d)$. Decompose into Schur sectors: each sector $\lambda$ has a sector code with Haar-average error $\overline{\delta}_{\lambda,n}$. Since $\sum_\lambda q_\lambda \overline{\delta}_{\lambda,n} \leq \delta_n$, define the "good set" $\mathcal{G}_n = \{\lambda : \overline{\delta}_{\lambda,n} \leq \sqrt{\delta_n}\}$. By Markov's inequality, $\sum_{\lambda \notin \mathcal{G}_n} q_\lambda \leq \sqrt{\delta_n}$.

### Step 2: Good $\cap$ Typical is nonempty

The typical set $\mathcal{T}_{p,n}$ carries mass $\geq 1 - o(1)$ (Sanov), and the good set carries mass $\geq 1 - \sqrt{\delta_n}$. For large $n$, these two sets must overlap: there exists a sequence $\lambda^{(n)} \in \mathcal{G}_n \cap \mathcal{T}_{p,n}$ with Haar-average sector error $\to 0$.

### Step 3: Koashi-Imoto per sector

For any fixed sector $\lambda$, the orbit ensemble $\{U_\lambda(g)\rho_\lambda U_\lambda(g)^\dagger : g \in U(d)\}$ generates the **full matrix algebra** $\mathcal{B}(H_\lambda)$. The proof proceeds by: (a) extracting the highest-weight projector $|v_\lambda\rangle\langle v_\lambda|$ as a polynomial in $\rho_\lambda$ (via Lagrange interpolation), (b) showing its orbit spans all of $H_\lambda$ by irreducibility, (c) concluding the commutant is trivial ($\mathfrak{A}_\lambda' = \mathbb{C} \cdot I$) so $\mathfrak{A}_\lambda = \mathcal{B}(H_\lambda)$ by the bicommutant theorem.

By the [[concepts/koashi-imoto|Koashi-Imoto structure theorem]], blind compression of an ensemble generating $\mathcal{B}(H_\lambda)$ requires memory $\geq \log \dim H_\lambda$. Therefore:

$$|M_n| \geq \log \dim H_{\lambda^{(n)}} + o(1)$$

### Step 4: Weyl dimension evaluation

Since $\lambda^{(n)} \in \mathcal{T}_{p,n}$, we have $\lambda_i^{(n)} = nx_i + O(\sqrt{n}\log n)$, and the [[concepts/weyl-dimension-formula|asymptotic Weyl dimension formula]] gives the matching lower bound.

## Related

- [[concepts/free-entropy|Free Entropy]] -- the information-theoretic quantity that governs QMDL
- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- governs the leading $\log n$ coefficient
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- the representation-theoretic decomposition
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- the key technical tool for achievability
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] -- converts irrep dimensions to the QMDL rate
- [[concepts/flag-manifold|Flag Manifold]] -- the geometric space whose dimension appears
- [[concepts/koashi-imoto|Koashi-Imoto Structure]] -- used in the converse proof
- [[concepts/schumacher-compression|Schumacher Compression]] -- the contrasting task that preserves purifications
