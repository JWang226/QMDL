# Converse (State Compression) (Theorem 3)

**Label:** `thm:converse` (Article)
**Source:** Article line ~762; Notes line ~1384

## Statement

Under the same conditions as [[results/achievability|Achievability (State Compression)]], any compression code sequence with vanishing error $\delta_n \to 0$ must have memory size:

$$\log|M_n| \geq \frac{r(2d-r-1)}{2}\log n + \sum_{i<j \leq r} \log(x_i - x_j) + (d-r)\sum_{i=1}^r \log x_i - \sum_{k=d-r}^{d-1} \log k! + o(1)$$

More precisely, the memory is bounded below by the minimum dimension among the typical Schur sectors:

$$|M_n| \geq \min_{\lambda \in \mathcal{T}_{p,n}} \log \dim \mathcal{H}_\lambda + o(1)$$

This **exactly matches** the achievability, proving optimality of the compression rate.

## Intuition

You cannot do better than the achievability protocol. The key insight is that within any single Schur sector $\lambda$, the orbit $\{U \rho_\lambda U^\dagger : U \in \mathrm{U}(d)\}$ generates the full operator algebra $\mathcal{B}(\mathcal{H}_\lambda)$. By the Koashi-Imoto structure theorem, this means the entire irrep space is "non-redundant" -- every qubit carries essential information about the eigenbasis. So you must store at least $\log \dim \mathcal{H}_\lambda$ qubits for each sector, and since this holds for at least one typical sector, it gives the lower bound.

## Proof Sketch

**Main idea:** Grant the encoder/decoder free access to the classical sector label $\lambda$ (this only makes the task easier). Use Markov's inequality on the Haar-averaged sector errors to find a "good" sector; intersect with the typical set to get a sector $\lambda^{(n)}$ that is both typical and well-compressed. For that sector, the orbit $\{U\rho_\lambda U^\dagger\}$ generates the full matrix algebra $\mathcal{B}(\mathcal{H}_\lambda)$ (via Lagrange interpolation + orbit spanning + bicommutant), so the Koashi-Imoto theorem forces $|M_n| \geq \log \dim \mathcal{H}_\lambda$. Evaluating with the asymptotic Weyl dimension formula gives the matching lower bound.

---

### Extended Proof

### Step 1: Decompose into Sector Codes

Apply the Schur transform to write $\rho_g^{\otimes n} = \sum_\lambda q_{\lambda,n} \, \rho_{g,\lambda} \otimes \tau_\lambda \otimes |\lambda\rangle\langle\lambda|$, where $q_{\lambda,n}$ depends only on the spectrum $x$ (not on $g$). Now pass to an easier "assisted" task: grant the encoder and decoder free access to the classical label $\lambda$, and allow them to discard the multiplicity state $\tau_\lambda$ before compression and recreate it for free afterward. Since this only adds free side information and ancillas, any lower bound for the assisted task is also a lower bound for the original task.

In the assisted task, the code decomposes blockwise: for each $\lambda$ there is a sector code $(\mathcal{E}_{\lambda,n}, \mathcal{D}_{\lambda,n})$ acting on $\mathcal{H}_\lambda$ alone, using the same shared memory $M_n$. Let $\delta_{\lambda,n}(g) = \frac{1}{2}\|\mathcal{D}_{\lambda,n} \circ \mathcal{E}_{\lambda,n}(\rho_{g,\lambda}) - \rho_{g,\lambda}\|_1$ be the sector error. Since the assisted task is easier, we can arrange:

$$\sup_{g \in \mathrm{U}(d)} \sum_\lambda q_{\lambda,n} \, \delta_{\lambda,n}(g) \leq \delta_n$$

### Step 2: Haar-Average Sector Errors

Average the sector error bound over the Haar measure on $\mathrm{U}(d)$. Define $\bar{\delta}_{\lambda,n} = \int_{\mathrm{U}(d)} dg \; \delta_{\lambda,n}(g)$. Then:

$$\sum_\lambda q_{\lambda,n} \, \bar{\delta}_{\lambda,n} \leq \delta_n$$

This weighted average of Haar-averaged sector errors is bounded by the overall error $\delta_n \to 0$.

### Step 3: Markov Inequality Defines the Good Set

Define the "good set" of sectors with small Haar-average error:

$$\mathcal{G}_n := \{\lambda : \ell(\lambda) \leq r, \; \bar{\delta}_{\lambda,n} \leq \sqrt{\delta_n}\}$$

By Markov's inequality applied to the bound in Step 2: $\sum_{\lambda \notin \mathcal{G}_n} q_{\lambda,n} \leq \sqrt{\delta_n}$. Thus the good set captures most of the probability mass: $\sum_{\lambda \in \mathcal{G}_n} q_{\lambda,n} \geq 1 - \sqrt{\delta_n}$.

### Step 4: Good $\cap$ Typical is Nonempty

Choose the typical set with $\Delta_n = \log n$:

$$\mathcal{T}_{p,n} := \{\lambda : \lambda_i = 0 \text{ for } i > r, \; \max_{1 \leq i \leq r} |\lambda_i - nx_i| \leq \sqrt{n} \log n\}$$

By [[results/remaining-lemmas|Sanov's Theorem (Lemma 12)]], $\sum_{\lambda \notin \mathcal{T}_{p,n}} q_{\lambda,n} \leq (n+1)^{r(r+1)/2} e^{-(\log n)^2/2} = o(1)$, so the typical set also captures most mass. Since the good set has mass $\geq 1 - \sqrt{\delta_n}$ and the typical set has mass $\geq 1 - o(1)$, for sufficiently large $n$ their total exceeds 1, so $\mathcal{G}_n \cap \mathcal{T}_{p,n} \neq \emptyset$.

Pick any sequence $\lambda^{(n)} \in \mathcal{G}_n \cap \mathcal{T}_{p,n}$. This sequence has both vanishing Haar-average sector error ($\bar{\delta}_{\lambda^{(n)},n} \leq \sqrt{\delta_n} \to 0$) and typical shape ($\lambda^{(n)}_i = nx_i + O(\sqrt{n} \log n)$).

### Step 5: Apply Koashi-Imoto (Prop 4)

For the specific sequence $\lambda^{(n)}$, the sector code has vanishing Haar-average error. [[results/remaining-lemmas|Irreducible Orbit Sector Compression (Prop 4)]] then implies:

$$|M_n| \geq \log \dim \mathcal{H}_{\lambda^{(n)}} + o(1)$$

The proof of Prop 4 proceeds in three stages:
1. **Lagrange interpolation:** The highest-weight eigenvalue of $\rho_\lambda$ is strictly larger than all others (since the spectrum $x$ has distinct entries), so the rank-one projector $|v_\lambda\rangle\langle v_\lambda|$ onto the highest-weight vector is a polynomial in $\rho_\lambda$: $|v_\lambda\rangle\langle v_\lambda| = \prod_{j \neq 1} (\rho_\lambda - x_j I)/(x_1 - x_j)$.
2. **Orbit spans:** The orbit $\{U_\lambda(g)|v_\lambda\rangle\langle v_\lambda|U_\lambda(g)^\dagger : g \in \mathrm{U}(d)\}$ consists of rank-one projectors, and their span is all of $\mathcal{H}_\lambda$ (since the linear span of $\{U_\lambda(g)|v_\lambda\rangle\}$ is a nonzero invariant subspace of the irrep, hence all of $\mathcal{H}_\lambda$).
3. **Bicommutant:** Any operator $X$ commuting with all these rank-one projectors must satisfy $X|u_g\rangle = a(g)|u_g\rangle$ for a continuous function $a(g)$ on connected $\mathrm{U}(d)$ taking values in $\mathrm{spec}(X)$ (a finite set), so $a$ is constant. Hence $X = a \cdot I$, proving the commutant is $\mathbb{C} \cdot I$ and (by finite-dimensional bicommutant) the generated algebra is $\mathcal{B}(\mathcal{H}_\lambda)$.

By the [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]], since the generated algebra is the full matrix algebra, the nonredundant quantum factor is the entire space $\mathcal{H}_\lambda$, and any compression with vanishing error must use memory $\geq \log \dim \mathcal{H}_\lambda$.

### Step 6: Evaluate with Weyl Dimension Formula

Since $\lambda^{(n)} \in \mathcal{T}_{p,n}$, we have $\lambda^{(n)}_i = nx_i + O(\sqrt{n} \log n)$ for $1 \leq i \leq r$ and $\lambda^{(n)}_i = 0$ for $i > r$. Applying [[results/remaining-lemmas|Asymptotic Weyl Dimension (Lemma 11)]] with $\Delta_n = \log n$:

$$\log \dim \mathcal{H}_{\lambda^{(n)}} = \frac{r(2d-r-1)}{2}\log n + \sum_{i<j \leq r} \log(x_i - x_j) + (d-r)\sum_{i=1}^r \log x_i - \sum_{k=d-r}^{d-1} \log k! + O\left(\frac{\log n}{\sqrt{n}}\right)$$

Since $\log n / \sqrt{n} = o(1)$, this gives the final converse bound matching the achievability rate.

## Dependencies

- [[results/remaining-lemmas|Irreducible Orbit Sector Compression (Prop 4)]] -- Koashi-Imoto based lower bound per sector
- [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]] -- the key structural result for blind compression
- [[results/remaining-lemmas|Asymptotic Weyl Dimension (Lemma 11)]] -- evaluates irrep dimensions asymptotically
- [[results/remaining-lemmas|Sanov's Theorem (Lemma 12)]] -- concentration of $\lambda$ around $nx$

## Used By

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- this is the converse half of the main result

## External References

- [Koashi and Imoto, "Compressibility of quantum mixed-state signals" (2001)](https://arxiv.org/abs/quant-ph/0101144)
