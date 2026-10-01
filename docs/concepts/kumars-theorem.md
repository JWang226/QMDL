# Kumar's Theorem

**Appears in:** [[Article]] (`sec:definition`; PRV background), [[Notes]] (Sec. 3.2)

## Statement

**(Kumar, 1988)** For dominant weights $\mu, \nu$ of a complex semisimple Lie group and any element $w$ of the Weyl group, the irreducible representation $V_{(\mu + w\nu)^+}$ appears in $V_\mu \otimes V_\nu$ with **multiplicity at least one**.

This was originally conjectured by Parthasarathy, Ranga Rao, and Varadarajan (1967) and proved by Kumar in 1988 using geometric methods from Borel-Weil theory. The components $V_{(\mu + w\nu)^+}$ are called **PRV components**.

## Clarification: Multiplicity $\geq 1$, Not Always $= 1$

Kumar's theorem guarantees **existence** ($c_{\mu\nu}^{(\mu+w\nu)^+} \geq 1$) for all Weyl group elements $w$. For a general Weyl group element $w$, the multiplicity can be greater than 1.

The special case that is most important for this project is $w = w_0$ (the **longest element** of the Weyl group). This is the original case studied by PRV, and the resulting component $\omega = (\mu + w_0\nu)^+$ is what is called the **[[concepts/prv-component|PRV component]]** in this wiki. For this particular case, the multiplicity is **exactly one**: $c_{\mu\nu}^{(\mu+w_0\nu)^+} = 1$.

The original PRV multiplicity-one theorem is a separate stronger statement for this distinguished component. A sum of two extremal weights is not necessarily an extremal vertex of the tensor-product weight polytope, so that observation alone is not a proof.

## Intuition

When you tensor two irreps $V_\mu \otimes V_\nu$, the result decomposes into many irreps. The Weyl group $W$ acts on the highest weight $\nu$, producing the orbit $\{w\nu : w \in W\}$. Translating by $\mu$ and projecting onto the dominant Weyl chamber gives the PRV components. The $w_0$ case (longest element) gives the **smallest** irrep in the decomposition under dominance ordering. Minimality in this order does not mean smallest dimension.

## Why Multiplicity One (for $w_0$) Matters

The multiplicity-one property for the $w_0$ component is **essential** for the [[concepts/generalized-cloning-map|Generalized Cloning Map]]:

1. **Uniqueness after selecting the component.** The Choi operator of the cloning map is the projector $\Pi_\omega$ onto the PRV component in $\mu^* \otimes \nu$. With multiplicity one, this projector is uniquely determined. With higher multiplicity, there would be a family of covariant channels.

2. **No free parameters.** Once the multiplicity-one PRV component is selected, its normalized Choi projector has no choice of copy. This does not assert uniqueness among all covariant channels or minimum ancilla dimension.

3. **Cartan embedding.** In the dominant-difference case, the isometry $V:H_\nu\to H_\mu\otimes H_\omega$ is unique up to phase. It gives a Stinespring dilation of the **reverse** partial-trace channel; the forward channel uses its normalized compression formula.

## Connection to the Littlewood-Richardson Rule

For $\mathrm{GL}(d, \mathbb{C})$, the decomposition of $V_\mu \otimes V_\nu$ is governed by Littlewood-Richardson coefficients $c_{\mu\nu}^\lambda$. Distinguish the two statements:

- Kumar's generalized existence theorem: $c_{\mu\nu}^{(\mu+w\nu)^+}\ge1$ for every $w\in W$.
- The original PRV multiplicity-one theorem: $c_{\mu\nu}^{(\mu+w_0\nu)^+}=1$ for the longest element.

For $\mathrm{GL}(2)$, the decomposition is multiplicity-free:

$$\mathrm{Sym}^j(\mathbb C^2)\otimes\mathrm{Sym}^k(\mathbb C^2)
\cong\bigoplus_{a=0}^{\min(j,k)}\det{}^a\otimes\mathrm{Sym}^{j+k-2a}(\mathbb C^2).$$

On restriction to $\mathrm{SU}(2)$, determinant twists disappear; the symmetric-power exponents still advance in steps of two.

For $d \geq 3$, generic coefficients can exceed 1, but the $w_0$ PRV component remains multiplicity-free.

## Formal Scope

The Lean proof constructs the relevant Cartan embedding and proves the forward and reverse PRV multiplicity-one statements for the actual supported partition pairs of Theorem 2, including signed dominant differences. It does not assume Kumar's theorem as an axiom and does not claim a formalization of the general theorem stated above. See [[concepts/prv-component]] and [[proof-structure]].

## References

- kumar1988proof: Kumar's original proof (Inventiones Math., 1988)
- parthasarathy1967: Original PRV conjecture (Annals of Math., 1967)

## Related

- [[concepts/prv-component|PRV Component]] -- the specific $w_0$ case used in the cloning map
- [[concepts/generalized-cloning-map|Generalized Cloning Map]] -- uses multiplicity one
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- the representation-theoretic framework
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] -- computes $\dim V_\omega$

## External References

- [Kumar, "Proof of the Parthasarathy-Ranga Rao-Varadarajan conjecture," *Inventiones Mathematicae* 93, 117--130 (1988)](https://doi.org/10.1007/BF01393689)
- [K. R. Parthasarathy, R. Ranga Rao, and V. S. Varadarajan, "Representations of complex semi-simple Lie groups and Lie algebras," *Annals of Mathematics* 85(3), 383--429 (1967)](https://doi.org/10.2307/1970351)
- [PRV conjecture (Wikipedia)](https://en.wikipedia.org/wiki/PRV_conjecture)
