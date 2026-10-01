# Koashi-Imoto Structure and the Approximate Converse

**Appears in:** [[Article]], opening of `sec:converse`; historical converse discussion in [[Notes]]. The current [[Letter]] refers to the Article for the matching converse.

## Exact Compression

The Koashi–Imoto theorem describes the structure of families of states under operations that preserve them exactly. A direct-sum decomposition separates the factors carrying state-dependent information from redundant factors that can be discarded and reconstructed.

This provides context for why irreducible orbit families resist compression. An exact structural result alone does not supply a uniform quantitative bound for a sequence of growing spaces with small, nonzero error.

## Current Article Converse

The current Article proves `prop:compact_orbit_memory` directly. Let $\tau_g=U(g)\tau U(g)^\dagger$ be an irreducible compact-group orbit on $H$. If $\tau$ has simple largest eigenvalue $p_0$, all other eigenvalues are at most $p_1$, and $\gamma=p_0-p_1>0$, then every encoder/decoder pair with Haar-average trace error $\overline\delta$ obeys

$$\dim M\ge\dim H\left(1-\frac{\overline\delta}{\gamma}\right).$$

The proof tests the recovered states against the orbit of the top eigenprojector and uses the Haar twirl $\int P_g\,dg=I/\dim H$. Positivity, trace preservation, and the operational trace-distance inequality give the memory bound.

The Lean theorem `OrbitTraceDistance.irreducible_orbit_memory_bound` proves this finite bound. `CanonicalOrbit` supplies actual canonical irreducibility and a spectrum-dependent uniform positive gap. `PhysicalCanonicalConverse` transfers any physical code to the padded target orbit using the proved forward/reverse comparison channels. Thus `FreeEntropy.theorem1_converse` assumes only vanishing Haar-average reconstruction error and concludes the exact QMDL liminf lower bound.

## Historical Argument

Earlier wiki and Notes discussions used Lagrange interpolation to extract a highest-weight projector, then an algebra-generation argument and Koashi–Imoto exact compression. That discussion should not be substituted for the current approximate converse. In particular, exact incompressibility at each fixed dimension does not by itself justify an $o(1)$ loss along growing dimensions.

## Related

- [[proof-structure]]
- [[results/converse|Converse (Article Theorem 1)]]
- [[concepts/schur-weyl-duality|Physical Irreducible Decomposition]]
- [[concepts/holevo-information|Holevo Information]]

## External References

- [Koashi and Imoto, “Operations that do not disturb partially known quantum states” (2002)](https://doi.org/10.1103/PhysRevA.66.022318)
