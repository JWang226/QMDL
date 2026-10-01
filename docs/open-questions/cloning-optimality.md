# Optimality of the Generalized Cloning Map

**Source:** Historical wiki/Notes discussion; current [[Article]], `thm:main`, `rem:prv_not_dim_min`.
**Status:** General channel optimality is not claimed by the current Article theorem or its Lean formalization.

## What Is Proved

Article Theorem 2 proves a finite **trace-distance upper bound** for the actual PRV/Cartan cloners on supported representation states with dominant difference. Both directions, covariance, the normalized Choi formulas, multiplicity one, and the Petz identity are formalized. These are not remaining construction gaps. See [[proof-structure]].

Theorem 1 proves the optimal asymptotic memory cost through its additive constant. Optimality of that memory cost does not imply that each local cloning channel minimizes every finite-input error criterion.

## Separate Optimization Questions

One may ask whether the PRV channel is optimal among covariant channels for a specified criterion: trace distance, fidelity, or overlap $\operatorname{Tr}[\mathcal N(\rho_\mu)\rho_\nu]$. These objectives are different. The earlier wiki attributed an overlap conjecture to a passage after “Proposition 3”; that attribution is not present in the current Article and should not be treated as a current numbered conjecture.

The PRV component is minimal in dominance order, but need not have the smallest dimension. Nor does choosing it alone establish any of these optimization statements. General covariant Choi operators can contain positive matrices on multiplicity spaces, so their optimization is not always a scalar mixture of irreducible projectors.

## Known Special Cases and Scope

The Article discusses Werner's pure-state cloner and PRV channels in purity amplification. Those special results do not settle arbitrary mixed representation-state objectives. A stronger optimization theorem would need to specify its input family, figure of merit, and admissible channels.

## Related

- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]]
- [[concepts/prv-component|PRV Component]]
- [[concepts/werners-cloning-map|Werner's Cloning Map]]
