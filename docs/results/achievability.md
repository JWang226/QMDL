# Achievability (State Compression) (Theorem 2)

**Label:** `thm:achievability` (Article), `thm:qudit_compression_fixed_p` (Notes)
**Source:** Article line ~490; Notes line ~1067

## Statement

Let $\rho$ be a rank-$r$ density matrix on $\mathbb{C}^d$ with non-degenerate positive eigenvalues $x_1 > \cdots > x_r > 0$. There exists a compression code sequence $(\mathcal{E}_n, \mathcal{D}_n)$ with:

**Memory size:**
$$\log|M_n| = \frac{r(2d-r-1)}{2}\log n + \sum_{i<j \leq r} \log(x_i - x_j) + (d-r)\sum_{i=1}^r \log x_i - \sum_{k=d-r}^{d-1} \log k! + o(1)$$

**Error:** $\delta_n = O(n^{-1/4 + \varepsilon})$ for any $\varepsilon > 0$.

More precisely, the error satisfies:
$$\delta_n \leq O(n^{-1/4 + \varepsilon}) + 2(n+1)^{r(r+1)/2} e^{-\Delta_n}$$
where $\Delta_n = (\log n)^2$ is a slowly growing function making the second term superpolynomially small.

## Intuition

You can compress $\rho^{\otimes n}$ into a quantum memory whose size grows only logarithmically in $n$. The leading coefficient $r(2d-r-1)/2$ counts the "effective dimension" of the eigenbasis manifold (it is the dimension of the Grassmannian of $r$-frames in $\mathbb{C}^d$), and the $O(1)$ correction depends on the eigenvalue spacings (larger gaps = more compressible). The protocol works by using [[concepts/schur-weyl-duality|Schur-Weyl Duality]] to decompose the tensor power into irreducible sectors, discarding the symmetric-group multiplicity (which carries no eigenbasis information), and mapping each sector to a single universal target irrep via the [[concepts/generalized-cloning-map|Generalized Cloning Map]].

## Proof Sketch

**Main idea:** Apply the Schur transform to decompose $\rho^{\otimes n}$ into irreducible sectors, discard the (uninformative) symmetric-group multiplicity, then clone each sector's GL-irrep state into a single universal target irrep $\Lambda^*$ via the generalized cloning map. The target $\Lambda^*$ is chosen with just enough padding ($O(\sqrt{n \log^2 n})$) so that $\Lambda^* - \lambda$ is dominant for every typical $\lambda$. The decoder reverses the cloning. Error has two parts: (1) atypical sectors contribute superpolynomially little (Sanov), and (2) typical sectors have cloning fidelity $1 - O(n^{-1/2+\varepsilon})$ by Theorem 1, giving trace distance $O(n^{-1/4+\varepsilon})$ via Fuchs-van de Graaf. The memory cost equals $\log \dim \mathcal{H}_{\Lambda^*}$, evaluated by the asymptotic Weyl dimension formula.

---

### Extended Proof

### The Encoder

The encoding protocol has four steps:

**Step 1 -- Schur transform.** Apply the Schur transform $V_{\mathrm{Schur}}$ to decompose $(\mathbb{C}^d)^{\otimes n}$. Since $\rho$ has rank $r$, the state $\rho^{\otimes n}$ is supported on irreps with at most $r$ rows:

$$\rho^{\otimes n} \simeq \bigoplus_{\lambda : \ell(\lambda) \leq r} q_{\lambda,n} \left(\rho_\lambda \otimes \tau_\lambda\right)$$

where $q_{\lambda,n}$ are the sector probabilities (depending only on the spectrum $x$), $\rho_\lambda$ is the GL-irrep state (carrying eigenbasis information), and $\tau_\lambda$ is the maximally mixed state on the symmetric-group multiplicity space $\mathcal{M}_\lambda$.

**Step 2 -- Measure $\lambda$ and discard $\mathcal{M}_\lambda$.** Measure which sector $\lambda$ the state belongs to (a non-destructive classical measurement on the label register). Then discard the multiplicity state $\tau_\lambda$ -- it is maximally mixed and independent of the eigenbasis $g$, so it carries no information worth compressing.

**Step 3 -- Clone to target irrep.** Apply the [[concepts/generalized-cloning-map|Generalized Cloning Map]] $\mathcal{C}_{\lambda \to \Lambda^*}$ to map $\rho_\lambda \in \mathcal{H}_\lambda$ into a single universal target representation $\mathcal{H}_{\Lambda^*}$. The target irrep is chosen to "dominate" all typical $\lambda$ simultaneously:

$$\Lambda^*_i := \lceil n x_i + (r - i)\xi_n \rceil, \qquad \xi_n = 2\sqrt{n\Delta_n / 2} + 1$$

The padding $\xi_n$ ensures that the weight difference $\Lambda^* - \lambda$ is a dominant weight for every typical $\lambda$. The key constraint is the gap condition: for the difference to form a valid Young diagram (non-increasing row lengths), we need $\Lambda^*_i - \Lambda^*_{i+1} \geq \lambda_i - \lambda_{i+1}$. The worst case occurs when adjacent rows fluctuate in opposite extreme directions, giving $\lambda_i - \lambda_{i+1} \leq n(x_i - x_{i+1}) + 2\epsilon_n$ where $\epsilon_n = \sqrt{n\Delta_n/2}$. Using the ceiling function inequality $\lceil a \rceil - \lceil b \rceil \geq a - b - 1$, the minimum guaranteed gap is $\Lambda^*_i - \Lambda^*_{i+1} \geq n(x_i - x_{i+1}) + \xi_n - 1$. The macroscopic terms cancel, leaving $\xi_n - 1 \geq 2\epsilon_n$, which is exactly satisfied by our choice $\xi_n = 2\epsilon_n + 1$. Note that $\Lambda^*$ partitions a slightly larger integer than $n$.

The complete encoder is:
$$\mathcal{E}_n(\cdot) = \sum_{\lambda : \ell(\lambda) \leq r} \mathcal{C}_{\lambda \to \Lambda^*} \circ \mathrm{Tr}_{\mathcal{M}_\lambda}(P_\lambda (\cdot) P_\lambda)$$

### The Decoder

The decoder reverses the process:
$$\mathcal{D}_n(\cdot) = \bigoplus_{\lambda : \ell(\lambda) \leq r} q_{\lambda,n} \left(\mathcal{C}_{\Lambda^* \to \lambda}(\cdot) \otimes \tau_\lambda\right)$$

For each sector: sample $\lambda'$ from the stored classical label, apply the reverse cloner $\mathcal{C}_{\Lambda^* \to \lambda'}$ to map back from the universal target to the original sector, and reattach a fresh maximally mixed multiplicity state $\tau_{\lambda'}$. Apply the inverse Schur transform to return to the original tensor product space.

### Error Analysis

The trace distance error decomposes cleanly thanks to the orthogonality of Schur sectors:

$$\delta_n = \sum_\lambda q_{\lambda,n} \frac{1}{2}\|\mathcal{C}_{\Lambda^* \to \lambda} \circ \mathcal{C}_{\lambda \to \Lambda^*}(\rho_\lambda) - \rho_\lambda\|_1$$

**Error split -- typical vs. atypical.** Define the typical set:

$$\mathcal{T}_{p,n} := \left\{\lambda : \lambda_i = 0 \text{ for } i > r, \; \max_{1 \leq i \leq r} |\lambda_i - x_i n| \leq \sqrt{n\Delta_n/2}\right\}$$

Then:

$$\delta_n \leq \underbrace{\max_{\lambda \in \mathcal{T}_{p,n}} \frac{1}{2}\|\mathcal{C}_{\Lambda^* \to \lambda} \circ \mathcal{C}_{\lambda \to \Lambda^*}(\rho_\lambda) - \rho_\lambda\|_1}_{\text{typical error}} + \underbrace{\sum_{\lambda \notin \mathcal{T}_{p,n}} q_{\lambda,n}}_{\text{atypical tail}}$$

**Atypical tail (Sanov).** By [[results/sanov-theorem|Sanov's Theorem (Lemma 12)]], the tail probability is bounded:

$$\delta_{\mathrm{tail}} \leq (n+1)^{r(r+1)/2} e^{-\Delta_n}$$

With $\Delta_n = (\log n)^2$, this is superpolynomially small.

**Typical error (cloning + Fuchs-van de Graaf).** For any typical $\lambda \in \mathcal{T}_{p,n}$, the distance to the target satisfies $d(\Lambda^*, \lambda) = O(\sqrt{n\Delta_n})$. Using the triangle inequality and contractivity of trace distance under CPTP maps:

$$\frac{1}{2}\|\mathcal{C}_{\Lambda^* \to \lambda} \circ \mathcal{C}_{\lambda \to \Lambda^*}(\rho_\lambda) - \rho_\lambda\|_1 \leq \frac{1}{2}\|\mathcal{C}_{\lambda \to \Lambda^*}(\rho_\lambda) - \rho_{\Lambda^*}\|_1 + \frac{1}{2}\|\mathcal{C}_{\Lambda^* \to \lambda}(\rho_{\Lambda^*}) - \rho_\lambda\|_1$$

By [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]], both cloning maps have fidelity $1 - O(n^{-1/2 + \varepsilon'})$. Applying the Fuchs-van de Graaf inequality $\frac{1}{2}\|\rho - \sigma\|_1 \leq \sqrt{2(1-F)}$, each trace distance is $O(n^{-1/4 + \varepsilon''})$.

### Memory Cost

Since the compressed state lives entirely in $\mathcal{H}_{\Lambda^*}$, the quantum memory is $|M_n| = \log d_{\Lambda^*}$. The components $\Lambda^*_i = nx_i + O(\sqrt{n\Delta_n})$ satisfy the hypotheses of [[results/remaining-lemmas|Asymptotic Weyl Dimension (Lemma 11)]] with sub-extensive fluctuations. The $O(\sqrt{n\Delta_n})$ shift vanishes into the $o(1)$ remainder, giving exactly the claimed memory formula. The three blocks of the Weyl dimension formula contribute: (1) $n^{r(r-1)/2}$ from nonzero-vs-nonzero row pairs, (2) $n^{r(d-r)}$ from nonzero-vs-zero row pairs (giving the eigenvalue terms), (3) a product of factorials from zero-vs-zero pairs (giving the $\log k!$ subtraction).

## Dependencies

- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] -- guarantees high-fidelity cloning between typical sectors and $\Lambda^*$
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- the decomposition into sectors
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- the encoding/decoding channel
- [[results/weyl-dimension-asymptotic|Asymptotic Weyl Dimension (Lemma 11)]] -- evaluates $\log \dim \mathcal{H}_{\Lambda^*}$ to get the memory size formula
- [[results/sanov-theorem|Sanov's Theorem (Lemma 12)]] -- concentration bound for atypical sectors

## Used By

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- this is the encoding half of the main result

## External References

- [Yang, Chiribella, and Hayashi, "Optimal compression for identically prepared qubit states" (2016)](https://doi.org/10.1103/PhysRevLett.117.090502)
- [Schumacher, "Quantum coding" (1995)](https://doi.org/10.1103/PhysRevA.51.2738)
