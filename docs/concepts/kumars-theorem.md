# Kumar's Theorem

**Appears in:** [[Article]] (Sec. 3.1, Prop. 5), [[Notes]] (Sec. 3.2)

## Statement

**(Kumar, 1988)** For dominant weights $\mu, \nu$ of a complex semisimple Lie group and any element $w$ of the Weyl group, the irreducible representation $V_{(\mu + w\nu)^+}$ appears in $V_\mu \otimes V_\nu$ with **multiplicity exactly one**.

This was originally conjectured by Parthasarathy, Ranga Rao, and Varadarajan (1967) -- hence these components are called **PRV components** -- and proved by Kumar in 1988 using geometric methods from Borel-Weil theory.

## Intuition

When you tensor two irreps $V_\mu \otimes V_\nu$, the result decomposes into many irreps via the Littlewood-Richardson rule. Most irreps can appear with multiplicity greater than one, meaning there are multiple linearly independent ways to embed that irrep into the tensor product. The PRV components are special: they sit at the "extremal" positions in the tensor product decomposition -- at the corners of the weight polytope -- and each appears exactly once.

### Geometric picture

Think of the weights of $V_\mu \otimes V_\nu$ as forming a polytope in weight space. The Weyl group $W$ acts on the highest weight $\nu$ of the second factor, producing the orbit $\{w\nu : w \in W\}$. Translating by $\mu$ gives the vertices $\mu + w\nu$, and projecting each onto the dominant Weyl chamber via $(\cdot)^+$ gives the PRV components. These sit at the "corners" of the tensor product polytope -- the extremal points where the Littlewood-Richardson coefficients are forced to be exactly 1 by the geometry of the weight diagram.

The most important PRV component for this project is the *minimal* one, obtained from the longest Weyl group element $w_0$: $\omega = (\mu + w_0\nu)^+ = (\nu - \mu)^+$ (using the identity $\mu^* = -w_0(\mu)$ in the dual formulation). This is the smallest irrep appearing in $\mu^* \otimes \nu$ under the dominance partial order.

## Why Multiplicity One Matters

The multiplicity-one property is **essential** for the [[concepts/generalized-cloning-map|Generalized Cloning Map]]:

1. **Uniqueness of the covariant channel.** By Schur's lemma, the Choi operator of any $\mathrm{U}(d)$-covariant channel $\mathcal{N}: \mathcal{B}(\mathcal{H}_\mu) \to \mathcal{B}(\mathcal{H}_\nu)$ is a convex combination of projectors onto the irreps in $\mu^* \otimes \nu$. If the PRV component $\omega$ appeared with multiplicity $k > 1$, the projector onto that isotypic component would be a rank-$k$ operator on the multiplicity space, and there would be a $k$-parameter family of covariant channels supported on that sector. With multiplicity one, the projector $\Pi_\omega$ is uniquely determined, and the generalized cloning map is the *unique* covariant channel of minimal average Casimir.

2. **No free parameters.** Without multiplicity one, one would need additional physical or mathematical criteria to select among the family of covariant channels. Kumar's theorem eliminates this ambiguity entirely: there is exactly one way to embed the PRV irrep into the tensor product, so the cloning map is canonical.

3. **Proof of trace preservation and optimality.** The proofs that the generalized cloner is trace-preserving and that it minimizes the Casimir (Article, Prop. 5) both rely on the fact that the PRV block is one-dimensional on the multiplicity side, so that $\Pi_\omega$ fully determines the channel.

## Connection to the Littlewood-Richardson Rule

For $\mathrm{GL}(d, \mathbb{C})$, the decomposition of $V_\mu \otimes V_\nu$ into irreps is governed by the Littlewood-Richardson coefficients $c_{\mu\nu}^\lambda$. Kumar's theorem states that $c_{\mu\nu}^{(\mu+w\nu)^+} = 1$ for every Weyl group element $w$.

In the special case of $\mathrm{GL}(2)$ (qubits), all irreps are symmetric powers $\mathrm{Sym}^k(\mathbb{C}^2)$ and the Littlewood-Richardson rule gives $\mathrm{Sym}^j \otimes \mathrm{Sym}^k \cong \bigoplus_{l=|j-k|}^{j+k} \mathrm{Sym}^l$, with every summand appearing with multiplicity one. So Kumar's theorem is automatically satisfied, and the generalized cloner reduces to Werner's optimal pure-state cloner.

For $d \geq 3$, Littlewood-Richardson coefficients can exceed 1 for generic irreps, but the PRV components remain multiplicity-free. This is what makes the construction work in full generality.

## References

- kumar1988proof: Kumar's original proof (Inventiones Math., 1988)
- parthasarathy1967: Original PRV conjecture (Annals of Math., 1967)

## Related

- [[concepts/prv-component|PRV Component]] -- the specific irrep $\omega = (\nu - \mu)^+$
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- uses multiplicity one to define the unique covariant channel
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- provides the representation-theoretic framework
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] -- computes $\dim V_\omega$ for the PRV component

## External References

- [Kumar, "Proof of the Parthasarathy-Ranga Rao-Varadarajan conjecture," *Inventiones Mathematicae* 93, 117--130 (1988)](https://doi.org/10.1007/BF01388456)
- K. R. Parthasarathy, R. Ranga Rao, and V. S. Varadarajan, "Representations of complex semi-simple Lie groups and Lie algebras," *Annals of Mathematics* 85(3), 383--429 (1967)
- [PRV conjecture (Wikipedia)](https://en.wikipedia.org/wiki/PRV_conjecture)
