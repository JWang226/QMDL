# Irreducible Orbit Sector Compression (Proposition 4)

**Label:** `prop:orbit_sector_converse`
**Source:** Article line ~666

## Statement

For any sequence of partitions $\{\lambda^{(n)}\}$, if a sector code achieves vanishing Haar-average error:

$$|M_n| \geq \log \dim \mathcal{H}_\lambda + o(1)$$

## Intuition

Within a single irrep sector, you cannot compress below $\log \dim \mathcal{H}_\lambda$ qubits. The orbit ensemble $\{U_\lambda(g)\rho_\lambda U_\lambda(g)^\dagger\}$ generates the full operator algebra $\mathcal{B}(\mathcal{H}_\lambda)$, so no quantum information is redundant.

## Proof Sketch

The proof establishes $\mathfrak{A}_\lambda = \mathcal{B}(\mathcal{H}_\lambda)$ in three steps:

**Step 1 (Lagrange interpolation).** Since the spectrum $x$ has distinct entries, the eigenvalues of $\rho_\lambda$ are distinct. The rank-one projector onto the highest-weight vector is a polynomial in $\rho_\lambda$: $|v_\lambda\rangle\langle v_\lambda| = \prod_{j \neq 1} (\rho_\lambda - x_j I)/(x_1 - x_j)$. By covariance, $U_\lambda(g)|v_\lambda\rangle\langle v_\lambda|U_\lambda(g)^\dagger \in \mathfrak{A}_\lambda$ for all $g$.

**Step 2 (Orbit spans $\mathcal{H}_\lambda$).** If $X$ commutes with every $|u_g\rangle\langle u_g|$, then $X|u_g\rangle = a(g)|u_g\rangle$ for some continuous $a: \mathrm{U}(d) \to \mathrm{spec}(X)$ (a finite set). Since $\mathrm{U}(d)$ is connected, $a$ is constant, so $X = aI$.

**Step 3 (Bicommutant theorem).** The commutant $\mathfrak{A}_\lambda' = \mathbb{C} \cdot I$, so by the bicommutant theorem, $\mathfrak{A}_\lambda = \mathcal{B}(\mathcal{H}_\lambda)$.

Finally, the [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]] for blind compression of mixed-state ensembles gives the per-sector memory lower bound $|M_n| \geq \log \dim \mathcal{H}_\lambda + o(1)$.

## Dependencies

- [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]]
- Bicommutant theorem

## Used By

- [[results/converse|Converse (State Compression)]] -- once a typical sector with vanishing error is identified, this gives the per-sector memory lower bound
