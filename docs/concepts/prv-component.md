# PRV Component (Parthasarathy-Ranga Rao-Varadarajan)

**Appears in:** [[Article]] (Sec. 3.1)

## Intuition

When you tensor two irreducible representations $H_\mu$ and $H_\nu$ of $\mathrm{GL}(d)$, the result decomposes into irreducible pieces (this is the Littlewood-Richardson decomposition). The PRV theorem guarantees that certain specific irreps appear in this decomposition with **multiplicity exactly one**. The most important is the "Cartan component" $(\mu + \nu)^+$, the dominant rearrangement of $\mu + \nu$.

For the generalized cloning map, the relevant PRV component is $\omega = (\nu - \mu)^+$ appearing in $\mu^* \otimes \nu$ -- this is the **minimal ancilla** needed to covariantly map from $H_\mu$ to $H_\nu$.

## Formal Statement (PRV Theorem)

Let $\mu, \nu$ be dominant weights of $\mathrm{GL}(d)$. For any element $w$ of the Weyl group $W$, the irrep $H_{(\mu + w\nu)^+}$ (the dominant rearrangement) appears in $H_\mu \otimes H_\nu$ with multiplicity at least one.

The **Cartan component** (taking $w = \mathrm{id}$) is $H_{(\mu + \nu)^+}$, which appears with multiplicity **exactly one**.

**Kumar's Theorem** (1988): The multiplicity-one property holds for all PRV components, not just the Cartan component. See [[concepts/kumars-theorem|Kumar's Theorem]].

## Role in the Cloning Map

For the [[concepts/generalized-cloning-map|Generalized Cloning Map]] $C_{\mu \to \nu}$:

1. Consider $H_{\mu^*} \otimes H_\nu$ where $\mu^* = (-\mu_d, \ldots, -\mu_1)$ is the contragredient
2. The PRV component $\omega = (\nu - \mu)^+$ appears with multiplicity one
3. The projector $\Pi_\omega$ onto this component defines the Choi operator: $J_\omega = (d_\mu / d_\omega) \Pi_\omega$
4. The intertwining isometry $V: H_\nu \to H_\mu \otimes H_\omega$ gives the Stinespring dilation

### Why multiplicity one matters

The multiplicity-one property is **essential** for two reasons:

- **Uniqueness of the Choi operator.** The cloning map is defined via the projector $\Pi_\omega$ onto the PRV component in $\mu^* \otimes \nu$. If $\omega$ appeared with multiplicity $> 1$, there would be a family of projectors (parameterized by how you choose the copy), and the cloning map would not be uniquely determined by covariance alone.

- **Clean Stinespring dilation.** The isometry $V: H_\nu \to H_\mu \otimes H_\omega$ intertwines the group actions: $V U_\nu(g) = (U_\mu(g) \otimes U_\omega(g)) V$ for all $g \in U(d)$. This intertwiner is unique up to a global phase precisely because the multiplicity is one. With higher multiplicity, you would need additional data to specify which embedding to use.

### Connection to Littlewood-Richardson coefficients

The multiplicity of an irrep $\lambda$ in $\mu \otimes \nu$ is the Littlewood-Richardson coefficient $c_{\mu\nu}^\lambda$. The PRV theorem guarantees $c_{\mu^* \nu}^\omega \geq 1$, and Kumar's theorem upgrades this to $c_{\mu^* \nu}^\omega = 1$ for the PRV component. The full Littlewood-Richardson decomposition of $\mu^* \otimes \nu$ has many other summands (corresponding to other covariant channels with larger ancillas), but the PRV component is distinguished as the unique minimum under dominance ordering.

## Worked Example: GL(3) Cloning

Take $\mu = (4, 2, 0)$ and $\nu = (5, 3, 1)$.

**Step 1: Compute $\mu^*$.** The contragredient (dual) representation has highest weight $\mu^* = (-\mu_d, -\mu_{d-1}, \ldots, -\mu_1)$. For GL(d), this becomes $(0, -2, -4)$ after negation and reversal. Reordering to make it dominant: $\mu^* \sim (0, -2, -4)$, but since we only care about $\nu - \mu$ for the PRV component, we compute directly.

**Step 2: Compute $\omega = (\nu - \mu)^+$.** The difference is $\nu - \mu = (5-4, 3-2, 1-0) = (1, 1, 1)$. This is already a dominant weight (weakly decreasing), so $\omega = (1, 1, 1)^+ = (1, 1, 1)$.

**Step 3: Identify the representation.** The irrep $(1, 1, 1)$ of GL(3) is the **determinant representation**: $U_{(1,1,1)}(g) = \det(g)$. It is 1-dimensional!

**Consequence:** The cloning map $C_{\mu \to \nu}$ uses a 1-dimensional ancilla. The isometry $V: H_\nu \to H_\mu \otimes \mathbb{C}$ is essentially a unitary equivalence (up to the determinant phase), making this the most efficient possible covariant channel. The Choi operator has rank $d_\omega = 1$, so the channel is as "clean" as possible.

**Why this happens geometrically:** The irreps $\mu = (4,2,0)$ and $\nu = (5,3,1)$ are "parallel" -- they differ by a uniform shift $(1,1,1)$. Shifting all rows of a Young diagram by the same amount corresponds to tensoring with the determinant, which is a 1-dimensional operation. This is the representation-theoretic version of the fact that multiplying a matrix by a scalar doesn't change its eigenbasis.

## Qubit Example: $d = 2$

For $d = 2$, $\mu = (n, 0)$, $\nu = (m, 0)$ with $m > n$:
- $\omega = (m - n, 0)$, the symmetric subspace $\mathrm{Sym}^{m-n}(\mathbb{C}^2)$
- The PRV component has dimension $m - n + 1$
- Recovers Werner's cloning map with Kraus rank $m - n + 1$

## Related

- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- constructed from the PRV component
- [[concepts/kumars-theorem|Kumar's Theorem]] -- proves multiplicity one for all PRV components
- [[concepts/kostant-partition-function|Kostant Partition Function]] -- related to weight multiplicities in the decomposition
- [[concepts/young-diagrams|Young Diagrams]] -- the combinatorial objects labeling irreps

## External References

- [K. R. Parthasarathy, R. Ranga Rao, and V. S. Varadarajan, "Representations of complex semi-simple Lie groups and Lie algebras," *Annals of Mathematics* 85(3), 383--429 (1967)](https://doi.org/10.2307/1970351)
- [Kumar, "Proof of the Parthasarathy-Ranga Rao-Varadarajan conjecture" (1988)](https://doi.org/10.1007/BF01393689)
- [Tensor product decomposition (Wikipedia)](https://en.wikipedia.org/wiki/Tensor_product_of_representations)
- [Littlewood-Richardson rule (Wikipedia)](https://en.wikipedia.org/wiki/Littlewood%E2%80%93Richardson_rule)
