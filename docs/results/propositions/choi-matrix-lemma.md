# Cartan Intertwiner and Choi Projector (Article Proposition 1)

**Label:** `prop:choi`; original channel definition `eq:gen_cloner`.
**Source:** [current Article](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L442). The Notes used the label `lem:choi_prv`; that is a separate version's reference.

## Statement

Let $\mu,\omega,\nu$ be dominant integral highest weights with $\nu=\mu+\omega$, and let $V:\mathcal H_\nu\to\mathcal H_\mu\otimes\mathcal H_\omega$ be the Cartan intertwining isometry. Then

$$
\mathcal C_{\mu\to\nu}(X)=\frac{d_\mu}{d_\nu}V^\dagger(X\otimes I_\omega)V
$$

has Choi operator

$$J=\frac{d_\mu}{d_\omega}\Pi_\omega$$

on $\mathcal H_\mu^*\otimes\mathcal H_\nu$, where $\Pi_\omega$ is the projector onto the multiplicity-one component of highest weight $\omega$. Consequently,

$$\mathcal C_{\mu\to\nu}(X)=\operatorname{Tr}_\mu[J(X^\top\otimes I_\nu)].$$

Here the difference $\nu-\mu$ is already dominant. The general PRV notation $(\nu-\mu)^+$ used elsewhere in the Article does not remove the Cartan hypothesis of this proposition.

## Intuition

The Cartan isometry and the Choi projector describe the same channel with different tensor indices grouped together. The first description makes Kraus branches available for the error proof; the second is the manuscript's original definition.

## Proof sketch

Reshuffle $V$ into a map $R:\mathcal H_\mu^*\otimes\mathcal H_\nu\to\mathcal H_\omega$. Expanding matrix entries gives $J=(d_\mu/d_\nu)R^\dagger R$. Intertwining and irreducibility make $RR^\dagger$ scalar on $\mathcal H_\omega$. Its trace is $d_\nu$, so

$$RR^\dagger=\frac{d_\nu}{d_\omega}I_\omega,\qquad
\Pi_\omega=\frac{d_\omega}{d_\nu}R^\dagger R.$$

The latter matrix is therefore an orthogonal projector of rank $d_\omega$. Highest-weight and intertwiner-space arguments identify its range and prove multiplicity one. Finally, an entrywise Choi contraction calculation recovers the map on every matrix.

Covariance alone only puts a Choi operator in the representation's commutant; it does not make every commuting operator a scalar multiple of this particular projector. The range and multiplicity arguments are essential.

## Lean coverage

The actual canonical representations needed for Theorem 2 are constructed for natural dominant $\mu,\nu$ with dominant **signed** difference. No Cartan isometry, PRV projector, dimension identity or multiplicity-one assertion is supplied to the final theorem as an assumption.

- [CanonicalChoi.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CanonicalChoi.lean): `FreeEntropy.ExteriorRepresentation.canonicalForward_choi`, `canonicalChoi_highest`, `canonicalChoi_cyclic_range`, and `canonicalChoi_multiplicity_one` in the same namespace.
- [ChoiContraction.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/ChoiContraction.lean): `FreeEntropy.CartanChoi.choiMap_eq_partialTraceInput`.
- [Theorem2Choi.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/Theorem2Choi.lean): `FreeEntropy.ExteriorRepresentation.prvForward_eq` and `prv_maps_are_channels` identify the literal formula with a CPTP map.

This is the Cartan family used by the main result. It is not a certificate of the Article's broader PRV existence statement for every arbitrary pair of irreducibles.

## Dependencies

- [[concepts/prv-component|PRV and Cartan components]]
- [[concepts/generalized-cloning-map|Generalized cloning map]]
- Constructed irreducible representations, Schur scalarity, and multiplicity one.

## Used By

- [[results/cloning-fidelity|Cloning accuracy (Article Theorem 2)]]
- [[results/propositions/reverse-cloner|Reverse cloner and Petz recovery]]
