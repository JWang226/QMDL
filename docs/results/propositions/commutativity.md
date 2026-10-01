# Commutativity (Article Proposition 3)

**Label:** `prop:commutativity` in the current Article; the Notes used `lem:commutativity`.
**Source:** [current Article](https://github.com/JWang226/QMDL/blob/main/article.tex#L589).

## Statement

Let $\rho$ have rank $r$, let $\mu,\nu$ be partitions with at most $r$ rows, and let $\mathcal N:\mathcal B(\mathcal H_\mu)\to\mathcal B(\mathcal H_\nu)$ be any $\mathrm U(d)$-covariant channel. Then

$$[\mathcal N(\rho_\mu),\rho_\nu]=0.$$

Here the states are the normalized representation states, not arbitrary matrices on the two representation spaces.

## Intuition and proof

In an eigenbasis of $\rho$, the input state is invariant under the diagonal unitary torus. Covariance makes the output torus-invariant too. Distinct torus characters separate weight spaces, so the output is block diagonal in those spaces. The target representation state is scalar on every weight space; it therefore commutes with the output.

Weight spaces may have multiplicity greater than one. The output need not already be diagonal in an arbitrarily chosen weight basis: it can be diagonalized further within each block. Likewise, strictly decreasing eigenvalues of $\rho$ do not imply that every eigenvalue of $\rho_\nu$ is distinct.

## Relation to the formal proof

The audited main endpoint is [[results/cloning-fidelity|Article Theorem 2]], whose direct trace-distance proof uses actual weight projectors, retained positive Kraus branches and positive remainders. It does not require a separately supplied general commutativity proposition or a classical fidelity calculation.

Relevant constructed ingredients include [TorusWeightProjection.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/TorusWeightProjection.lean), [CanonicalOrbit.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalOrbit.lean), and the proved channel covariance in [CanonicalCloningOrbit.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalCloningOrbit.lean). For example, `FreeEntropy.ExteriorRepresentation.canonicalForward_covariant` treats the actual forward channel.

There is no separately indexed Lean endpoint here certifying Proposition 3 for **every** covariant channel. Its short mathematical proof is recorded above; the existence of the supporting torus and covariance modules should not be read as a claim that the whole proposition was packaged and audited as a standalone theorem.

## Dependencies

- [[definitions/covariant-channel|Covariant channel]]
- Torus characters and representation weight spaces.

## Used By

- Structural interpretation of [[concepts/generalized-cloning-map|generalized cloning]].
- Historical fidelity-based discussions; it is not an extra premise of the current finite trace-distance endpoint.
